
all: rcg srcg rcgToPerpl

rcg: rcg.hs
	ghc -main-is RCG.main rcg

srcg: srcg.hs rcg.hs
	ghc -main-is SRCG.main srcg.hs rcg.hs

rcgToPerpl: rcgToPerpl.hs rcg.hs
	ghc -main-is RCGtoPERPL.main rcgToPerpl.hs rcg.hs

clean:
	rm -f rcg srcg rcgToPerpl *.hi *.o
