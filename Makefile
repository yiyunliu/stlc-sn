LIBNAME=WR

coq: CoqSrc.mk $(VFILES)
	$(MAKE) -f CoqSrc.mk

%.vo: %.v CoqSrc.mk
	$(MAKE) -f CoqSrc.mk $*.vo

vos:  CoqSrc.mk
	@$(MAKE) -f CoqSrc.mk vos

%.vos:  %.v CoqSrc.mk
	@$(MAKE) -f CoqSrc.mk $*.vos

syntax.v : syntax.sig
	as2-exe -i syntax.sig -p Coq > syntax.v
	perl -i -pe 's/^(Hint|Instance)/#[export]$1/' syntax.v

usyntax.v : syntax.sig
	as2-exe -i syntax.sig -p UCoq > usyntax.v
	perl -i -pe 's/^(Hint|Instance)/#[export]$1/' usyntax.v

_CoqProject : usyntax.v syntax.v *.v
	{ echo "-R . $(LIBNAME) " ; ls *.v ; } > _CoqProject

CoqSrc.mk: _CoqProject
	 coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk

.PHONY: clean
clean:
	rm -f syntax.v
	$(MAKE) -f CoqSrc.mk clean
