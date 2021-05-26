bench_rsa_sign:
	python3 ./run_bench.py rsa sign

bench_rsa_verify:
	python3 ./run_bench.py rsa verify

bench_class_sign:
	python3 ./run_bench.py class sign

bench_class_verify:
	python3 ./run_bench.py class verify

bench: bench_rsa_sign bench_rsa_verify bench_class_sign bench_class_verify

.PHONY: bench clean bench_rsa_sign bench_rsa_verify bench_class_sign bench_class_verify
