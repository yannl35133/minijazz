all:
	dune build
	ln -fs _build/default/main/mjc.bc mjc.byte

clean:
	dune clean
	@rm -f mjc.byte
