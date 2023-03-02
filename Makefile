
rcg: rcg.hs
	ghc -main-is RCG.main rcg

srcg: srcg.hs rcg.hs
	ghc -main-is SRCG.main srcg.hs rcg.hs

all: rcg.hs srcg.hs

clean:
	rm -f rcg srcg *.hi *.o
