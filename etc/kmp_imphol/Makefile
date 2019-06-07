all: kmp

kmp: KMP.mlb KMP.sml KMP_Code_Export.sml Unsynchronized.sml
	~/opt/mlton2018/bin/mlton -verbose 1 -default-type int64 -output kmp KMP.mlb
