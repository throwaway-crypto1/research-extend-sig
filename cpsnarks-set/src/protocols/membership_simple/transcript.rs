use crate::{
    channels::ChannelError,
    commitments::{integer::IntegerCommitment, Commitment},
    protocols::{
        membership_simple::{
            channel::{MembershipProverChannel, MembershipVerifierChannel},
            Proof, CRS,
        },
        modeq::{
            channel::{ModEqProverChannel, ModEqVerifierChannel},
            transcript::{
                TranscriptProtocolModEq, TranscriptProverChannel as ModEqTranscriptProverChannel,
                TranscriptVerifierChannel as ModEqTranscriptVerifierChannel,
            },
        },
        root::{
            channel::{RootProverChannel, RootVerifierChannel},
            transcript::{
                TranscriptProtocolRoot, TranscriptProverChannel as RootTranscriptProverChannel,
                TranscriptVerifierChannel as RootTranscriptVerifierChannel,
            },
        },
    },
    transcript::{TranscriptChannelError, TranscriptProtocolChallenge, TranscriptProtocolInteger},
    utils::{curve::CurvePointProjective, ConvertibleUnknownOrderGroup},
};
use merlin::Transcript;
use rug::Integer;
use std::cell::RefCell;

use serde::Serialize;

pub trait TranscriptProtocolMembership<G: ConvertibleUnknownOrderGroup>:
    TranscriptProtocolInteger<G> + TranscriptProtocolChallenge
{
    fn membership_domain_sep(&mut self);
}

impl<G: ConvertibleUnknownOrderGroup> TranscriptProtocolMembership<G> for Transcript {
    fn membership_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"membership");
    }
}
pub struct TranscriptVerifierChannel<
    'a,
    G: ConvertibleUnknownOrderGroup + Serialize,
    P: CurvePointProjective + Serialize,
    T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
> {
    transcript: &'a RefCell<T>,
    c_e: Option<<IntegerCommitment<G> as Commitment>::Instance>,
    root_transcript_verifier_channel: RootTranscriptVerifierChannel<'a, G, T>,
    modeq_transcript_verifier_channel: ModEqTranscriptVerifierChannel<'a, G, P, T>,
}

impl<
        'a,
        G: ConvertibleUnknownOrderGroup + Serialize,
        P: CurvePointProjective + Serialize,
        T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
    > TranscriptVerifierChannel<'a, G, P, T>
{
    pub fn new(
        crs: &CRS<G, P>,
        transcript: &'a RefCell<T>,
    ) -> TranscriptVerifierChannel<'a, G, P, T> {
        TranscriptVerifierChannel {
            transcript,
            c_e: None,
            root_transcript_verifier_channel: RootTranscriptVerifierChannel::new(
                &crs.crs_root,
                transcript,
            ),
            modeq_transcript_verifier_channel: ModEqTranscriptVerifierChannel::new(
                &crs.crs_modeq,
                transcript,
            ),
        }
    }

    pub fn proof(&self) -> Result<Proof<G, P>, TranscriptChannelError> {
        let proof_root = self.root_transcript_verifier_channel.proof()?;
        let proof_modeq = self.modeq_transcript_verifier_channel.proof()?;
        if self.c_e.is_some() {
            Ok(Proof {
                c_e: self.c_e.as_ref().unwrap().clone(),
                proof_root,
                proof_modeq,
            })
        } else {
            Err(TranscriptChannelError::Incomplete)
        }
    }
}

impl<
        'a,
        G: ConvertibleUnknownOrderGroup + Serialize,
        P: CurvePointProjective + Serialize,
        T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
    > RootVerifierChannel<G> for TranscriptVerifierChannel<'a, G, P, T>
{
    fn send_message1(
        &mut self,
        message: &crate::protocols::root::Message1<G>,
    ) -> Result<(), ChannelError> {
        self.root_transcript_verifier_channel.send_message1(message)
    }
    fn send_message2(
        &mut self,
        message: &crate::protocols::root::Message2<G>,
    ) -> Result<(), ChannelError> {
        self.root_transcript_verifier_channel.send_message2(message)
    }
    fn send_message3(
        &mut self,
        message: &crate::protocols::root::Message3,
    ) -> Result<(), ChannelError> {
        self.root_transcript_verifier_channel.send_message3(message)
    }
    fn receive_challenge(&mut self) -> Result<Integer, ChannelError> {
        self.root_transcript_verifier_channel.receive_challenge()
    }
}

impl<
        'a,
        G: ConvertibleUnknownOrderGroup + Serialize,
        P: CurvePointProjective + Serialize,
        T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
    > ModEqVerifierChannel<G, P> for TranscriptVerifierChannel<'a, G, P, T>
{
    fn send_message1(
        &mut self,
        message: &crate::protocols::modeq::Message1<G, P>,
    ) -> Result<(), ChannelError> {
        self.modeq_transcript_verifier_channel
            .send_message1(message)
    }
    fn send_message2(
        &mut self,
        message: &crate::protocols::modeq::Message2<P>,
    ) -> Result<(), ChannelError> {
        self.modeq_transcript_verifier_channel
            .send_message2(message)
    }
    fn receive_challenge(&mut self) -> Result<Integer, ChannelError> {
        self.modeq_transcript_verifier_channel.receive_challenge()
    }
}

pub struct TranscriptProverChannel<
    'a,
    G: ConvertibleUnknownOrderGroup + Serialize,
    P: CurvePointProjective + Serialize,
    T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
> {
    transcript: &'a RefCell<T>,
    root_transcript_prover_channel: RootTranscriptProverChannel<'a, G, T>,
    modeq_transcript_prover_channel: ModEqTranscriptProverChannel<'a, G, P, T>,
    proof: Proof<G, P>,
}

impl<
        'a,
        G: ConvertibleUnknownOrderGroup + Serialize,
        P: CurvePointProjective + Serialize,
        T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
    > RootProverChannel<G> for TranscriptProverChannel<'a, G, P, T>
{
    fn receive_message1(&mut self) -> Result<crate::protocols::root::Message1<G>, ChannelError> {
        self.root_transcript_prover_channel.receive_message1()
    }
    fn receive_message2(&mut self) -> Result<crate::protocols::root::Message2<G>, ChannelError> {
        self.root_transcript_prover_channel.receive_message2()
    }
    fn receive_message3(&mut self) -> Result<crate::protocols::root::Message3, ChannelError> {
        self.root_transcript_prover_channel.receive_message3()
    }
    fn generate_and_send_challenge(&mut self) -> Result<Integer, ChannelError> {
        self.root_transcript_prover_channel
            .generate_and_send_challenge()
    }
}

impl<
        'a,
        G: ConvertibleUnknownOrderGroup + Serialize,
        P: CurvePointProjective + Serialize,
        T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
    > ModEqProverChannel<G, P> for TranscriptProverChannel<'a, G, P, T>
{
    fn receive_message1(
        &mut self,
    ) -> Result<crate::protocols::modeq::Message1<G, P>, ChannelError> {
        self.modeq_transcript_prover_channel.receive_message1()
    }
    fn receive_message2(&mut self) -> Result<crate::protocols::modeq::Message2<P>, ChannelError> {
        self.modeq_transcript_prover_channel.receive_message2()
    }
    fn generate_and_send_challenge(&mut self) -> Result<Integer, ChannelError> {
        self.modeq_transcript_prover_channel
            .generate_and_send_challenge()
    }
}

impl<
        'a,
        G: ConvertibleUnknownOrderGroup + Serialize,
        P: CurvePointProjective + Serialize,
        T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
    > MembershipVerifierChannel<G> for TranscriptVerifierChannel<'a, G, P, T>
{
    fn send_c_e(
        &mut self,
        c_e: &<IntegerCommitment<G> as Commitment>::Instance,
    ) -> Result<(), ChannelError> {
        let mut transcript = self.transcript.try_borrow_mut()?;
        transcript.membership_domain_sep();
        transcript.append_integer_point(b"c_e", c_e);
        self.c_e = Some(c_e.clone());
        Ok(())
    }
}

impl<
        'a,
        G: ConvertibleUnknownOrderGroup + Serialize,
        P: CurvePointProjective + Serialize,
        T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
    > MembershipProverChannel<G> for TranscriptProverChannel<'a, G, P, T>
{
    fn receive_c_e(
        &mut self,
    ) -> Result<<IntegerCommitment<G> as Commitment>::Instance, ChannelError> {
        let mut transcript = self.transcript.try_borrow_mut()?;
        transcript.membership_domain_sep();
        transcript.append_integer_point(b"c_e", &self.proof.c_e);
        Ok(self.proof.c_e.clone())
    }
}

impl<
        'a,
        G: ConvertibleUnknownOrderGroup + Serialize,
        P: CurvePointProjective + Serialize,
        T: TranscriptProtocolMembership<G> + TranscriptProtocolRoot<G> + TranscriptProtocolModEq<G, P>,
    > TranscriptProverChannel<'a, G, P, T>
{
    pub fn new(
        crs: &CRS<G, P>,
        transcript: &'a RefCell<T>,
        proof: &Proof<G, P>,
    ) -> TranscriptProverChannel<'a, G, P, T> {
        TranscriptProverChannel {
            transcript,
            root_transcript_prover_channel: RootTranscriptProverChannel::new(
                &crs.crs_root,
                transcript,
                &proof.proof_root,
            ),
            modeq_transcript_prover_channel: ModEqTranscriptProverChannel::new(
                &crs.crs_modeq,
                transcript,
                &proof.proof_modeq,
            ),
            proof: proof.clone(),
        }
    }
}
