miracula: miracula.sml miracula.mlb
	mlton miracula.mlb
clean:
	rm -f ./miracula
test: miracula
	./test_runner.sh
