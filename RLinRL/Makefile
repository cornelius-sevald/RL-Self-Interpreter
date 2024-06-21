RL=PERevFlow-exe

SINT=sint.rl
SINT_OPT=sint_opt.rl
SINT_INV=sint_inv.rl

PROGS=$(wildcard progs/*.rl)
SPECS=$(wildcard progs/*.spec)
INV_PROGS=$(patsubst progs/%,inv_progs/%,$(PROGS))
INV_SPECS=$(patsubst progs/%,inv_progs/%,$(SPECS))
PREP_PROGS=$(patsubst progs/%,prep_progs/%,$(SPECS))

.PHONY: all preprocess invert clean

all: preprocess invert

preprocess: $(PREP_PROGS)

invert: $(INV_PROGS) $(INV_SPECS) $(SINT_INV)

$(SINT_OPT): $(SINT)
	$(RL) optimize $< $@

$(SINT_INV): $(SINT_OPT)
	$(RL) invert $< $@

prep_progs/%.spec: progs/%.rl progs/%.spec
	$(RL) preprocess $^ $@

inv_progs/%.rl: progs/%.rl
	$(RL) invert $< $@

inv_progs/%.spec: progs/%.rl progs/%.spec
	$(RL) interpret -v $^ | head -n-2 | sed "s/: / = '/" > $@

clean:
	rm -f $(PREP_PROGS)
	rm -f $(INV_PROGS)
	rm -f $(INV_SPECS)
