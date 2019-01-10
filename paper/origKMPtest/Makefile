all: kmp

kmp: KMP.mlb KMP.sml KMP_Code_Export.sml Unsynchronized.sml
	mlton -verbose 1 -default-type int64 -output kmp KMP.mlb

lorem.txt: lorem0.txt
	rm -f lorem.txt
	bash -c 'for ((i=0;$$i<100;++i)); do cat lorem0.txt >> lorem.txt; done'

bench: kmp lorem.txt
	time -v ./kmp 200 'not a latin text' 'lorem.txt'
