
rcg: rcg.hs
	ghc -main-is RCG.main rcg

all: rcg.hs

clean:
	rm -f rcg rcg.hi rcg.o
