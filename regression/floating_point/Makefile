all: fp_test

fp_test: FP_test.mlb FP_test_base.sml FP_test_parser.sml
	mlton -verbose 1 -default-type int64 -output fp_test FP_test.mlb

results.txt: mktests.sh fp_test make_results.sh
	./make_results.sh > results.txt

#
# FP_test_defs.sml: ./mktests.sh ./__mktest.awk
# 	./mktests.sh > FP_test_defs.sml
