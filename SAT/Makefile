3_6_12.opb: e.py
	python3 e.py --pb 3 6 12 > $@

3_6_12_sym.opb: ppr2veripb.py 3_6_12.opb 3_6_12.ppr
	cp 3_6_12.opb $@
	python3 ppr2veripb.py 3_6_12.ppr >/dev/null 2>>$@

3_6_12_sym_proof.opb: ppr2veripb.py 3_6_12.ppr
	python3 ppr2veripb.py 3_6_12.ppr >$@ 2>/dev/null

all: 3_6_12.opb 3_6_12_sym.opb 3_6_12_sym_proof.opb
