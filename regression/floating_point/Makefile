all: fp_test

.PHONY: test_semantics

fp_test: FP_test.mlb FP_test_base.sml FP_test_parser.sml
	mlton -verbose 1 -default-type int64 -output fp_test FP_test.mlb

tests.txt: mktests.sh
	./mktests.sh > tests.txt

fixed_tests.txt: tests.txt
	../bin/test_float_ops fix <tests.txt >fixed_tests.txt

test_semantics: fp_test fixed_tests.txt
	pv fixed_tests.txt | ./fp_test


# results.txt: tests.txt
# 	./make_results.sh > results.txt

#
# FP_test_defs.sml: ./mktests.sh ./__mktest.awk
# 	./mktests.sh > FP_test_defs.sml
