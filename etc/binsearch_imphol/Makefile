all: bs

bs: BS.mlb BS.sml BS_Code_Export.sml Unsynchronized.sml
	mlton -verbose 1 -default-type int64 -output bs BS.mlb
