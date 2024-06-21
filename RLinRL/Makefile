RL=PERevFlow-exe

SINT=sint.rl
SINT_OPT=sint_opt.rl
SINT_INV=sint_inv.rl
SINT_INV_OPT=sint_inv_opt.rl

PROGS=$(wildcard progs/*.rl)
SPECS=$(wildcard progs/*.spec)
INV_PROGS=$(patsubst progs/%,inv_progs/%,$(PROGS))
INV_SPECS=$(patsubst progs/%,inv_progs/%,$(SPECS))
PREP_PROGS=$(patsubst progs/%,prep_progs/%,$(SPECS))
PREP_PROGS_REV=$(patsubst progs/%,prep_progs_rev/%,$(SPECS))
PREP_INV_PROGS=$(patsubst inv_progs/%,prep_inv_progs/%,$(INV_SPECS))
PREP_INV_PROGS_REV=$(patsubst inv_progs/%,prep_inv_progs_rev/%,$(INV_SPECS))

.PHONY: all preprocess invert clean

all: preprocess invert

preprocess: $(PREP_PROGS) $(PREP_INV_PROGS) $(PREP_PROGS_REV) $(PREP_INV_PROGS_REV)

invert: $(INV_PROGS) $(INV_SPECS) $(SINT_INV) $(SINT_INV_OPT)

$(SINT_OPT): $(SINT)
	$(RL) optimize $< $@

$(SINT_INV): $(SINT)
	$(RL) invert $< $@

$(SINT_INV_OPT): $(SINT_OPT)
	$(RL) invert $< $@

inv_progs/%.rl: progs/%.rl
	$(RL) invert $< $@

inv_progs/%.spec: progs/%.rl progs/%.spec
	$(RL) interpret -v $^ | head -n-2 | sed "s/: / = '/" > $@

prep_progs/%.spec: progs/%.rl progs/%.spec
	$(RL) preprocess $^ $@

prep_progs_rev/%.spec: progs/%.rl inv_progs/%.spec
	$(RL) preprocess -v $^ /dev/stdout | sed 's/^input/output/' > $@

prep_inv_progs/%.spec: inv_progs/%.rl inv_progs/%.spec
	$(RL) preprocess $^ $@

prep_inv_progs_rev/%.spec: inv_progs/%.rl progs/%.spec
	$(RL) preprocess -v $^ /dev/stdout | sed 's/^input/output/' > $@

clean:
	rm -f $(PREP_PROGS)
	rm -f $(PREP_PROGS_REV)
	rm -f $(PREP_INV_PROGS)
	rm -f $(PREP_INV_PROGS_REV)
	rm -f $(INV_PROGS)
	rm -f $(INV_SPECS)
	rm -f $(SINT_OPT)
	rm -f $(SINT_INV)
	rm -f $(SINT_OPT)
