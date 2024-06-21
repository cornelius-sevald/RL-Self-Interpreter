RL Self-Interpreter
===================

Before running the Makefile, you must have
<https://github.com/cornelius-sevald/PERevFlow/tree/preprocess>
installed.

Files:
 - sint.rl:             The self-interpreter.
 - sint_inv.rl:         Inverted version of `sint.rl`.
 - sint_opt.rl:         Optimized version of `sint.rl`.
 - sint_inv_opt.rl:     Inverse optimized version of `sint.rl`,
                        i.e. inverse version of `sint_opt.rl`.

Folders:
  - progs:              Some test RL programs.
  - inv_progs:          Inversed versions of `progs`.
  - prep_progs:         Preprocessed version of `progs`.
  - prep_progs_rev:     Preprocessed version of `progs` with inverse store,
                        can be interpreted by `sint_inv.rl`.
  - prep_int_progs:     Preprocessed version of `inv_progs`.
  - prep_int_progs_rev: Preprocessed version of `inv_progs` with inverse (i.e. normal) store,
                        can be interpreted by `sint_inv.rl`.
