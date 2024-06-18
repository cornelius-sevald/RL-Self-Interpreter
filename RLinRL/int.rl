(prog input)
->
(prog output trace)
with
(BLOCK STEP LABEL COMES STEPS SPETS JUMP BLOCKS SKCOLB STORE EROTS LABEL_TO_FIND VAR_TO_FIND LOOKUP EXPR EXPR_TYPE EXPR_RES FLAG FLAG_EVAL COMES_TYPE JUMP_TYPE PREV_LABEL trace_TMP)

// Meanings of variables:
// - prog: input program
// - input: initial store
// - output: final store
// - trace: list of blocks visited (only for debugging)
// - BLOCK: The current block. Is often 'nil as it is deconstructed into LABEL, COMES, STEPS & JUMP
// - BLOCKS: List of blocks of the program.
// - SKCOLB: List that temporarily hold blocks of the program in reverse order (hence the name)
// - STORE: Current store of the program.
// - EROTS: List that temporarily holds variable/value pairs from the store in reverse order (hence the name)
// - LABEL_TO_FIND: When performing a non-exit jump, the label of the block to find.
// - VAR_TO_FIND: When doing a variable lookup, the variable to find.
// - EXPR: Current expression that is to be- or has just been evaluated.
// - EXPR_RES: The result of evaluating an expression
// - FLAG: (BAD NAME) Value used to know where to jump to / come from when jumping to the same block from many sources.
// - FLAG_EVAL: True if an expression has been evaluated and needs to be un-evaluated.

// READ:
// Think I should let `SKCOLB` (terrible name) be non-nil,
// right up until I have to find the new block. Then restore it
// onto `BLOCKS` and search.

init:
entry
  // Preprocessed programs always have the entry block first
  (BLOCK . BLOCKS) <- prog
  (LABEL . (COMES . (STEPS . JUMP))) <- BLOCK
  STORE <- input
goto main_loop

main_loop:
fi COMES = 'ENTRY from init else find_block2
  // TODO: remove debug trace
  trace_TMP ^= LABEL
  trace <- (trace_TMP . trace)
goto do_come_from

// Look up VAR_TO_FIND,
// storing the resulting variable/value pair in LOOKUP.
do_lookup:
from eval_var
goto do_lookup1

do_lookup1:
fi EROTS from do_lookup2 else do_lookup
  (LOOKUP . STORE) <- STORE
if hd LOOKUP = VAR_TO_FIND goto done_lookup else do_lookup2

do_lookup2:
from do_lookup1
  EROTS <- (LOOKUP . EROTS)
goto do_lookup1

done_lookup:
from do_lookup1
goto eval_var1

// Restore LOOKUP back to store and EROTS back to STORE.
undo_lookup:
from eval_var1
goto undo_lookup1

undo_lookup1:
fi hd LOOKUP = VAR_TO_FIND from undo_lookup else undo_lookup2
  STORE <- (LOOKUP . STORE)
if EROTS goto undo_lookup2 else undone_lookup

undo_lookup2:
from undo_lookup1
  assert(EROTS)
  (LOOKUP . EROTS) <- EROTS
goto undo_lookup1

undone_lookup:
from undo_lookup1
goto eval_var2

// evaluate expression of `if` jump
do_eval_if:
fi FLAG_EVAL from do_if4 else do_if 
  assert(FLAG = 'nil)
  FLAG ^= 'IF
goto do_eval_junction

// evaluate expression of `fi` come-from
do_eval_fi:
fi FLAG_EVAL from do_fi4 else do_fi 
  assert(FLAG = 'nil)
  FLAG ^= 'FI
goto do_eval_junction

// Junction block of `do_eval_if` and `do_eval_fi`
do_eval_junction:
fi FLAG = 'IF from do_eval_if else do_eval_fi
goto do_eval

// Evaluate the expression in EXPR,
// and store the result in EXPR_RES.
do_eval:
from do_eval_junction
  assert(EXPR_TYPE = 'nil)
  EXPR_TYPE ^= hd EXPR
if EXPR_TYPE = 'CONST goto eval_const else do_eval1

do_eval1:
from do_eval
  // TODO: implement more expression types
  assert(EXPR_TYPE = 'VAR)
goto eval_var

// Evaluate a constant
eval_const:
from do_eval
  assert(EXPR_TYPE = 'CONST)
  EXPR_RES ^= tl EXPR
goto done_eval

// Evaluate a variable
eval_var:
from do_eval1
  assert(EXPR_TYPE = 'VAR)
  VAR_TO_FIND ^= tl EXPR
goto do_lookup

eval_var1:
from done_lookup
  EXPR_RES ^= tl LOOKUP
goto undo_lookup

eval_var2:
from undone_lookup
  VAR_TO_FIND ^= tl EXPR
goto done_eval1

done_eval1:
from eval_var2
  // TODO: implement more expression types
  assert(EXPR_TYPE = 'VAR)
goto done_eval

// cleanup after evaluating expression
done_eval:
fi EXPR_TYPE = 'CONST from eval_const else done_eval1
  EXPR_TYPE ^= hd EXPR
goto done_eval_junction

// Junction block of `done_eval_if` and `done_eval_fi`
done_eval_junction:
from done_eval
if FLAG = 'IF goto done_eval_if else done_eval_fi

done_eval_if:
from done_eval_junction
  assert(FLAG = 'IF)
  FLAG ^= 'IF
  // Toggle eval flag.
  FLAG_EVAL ^= 'true
goto do_if1

done_eval_fi:
from done_eval_junction
  assert(FLAG = 'FI)
  FLAG ^= 'FI
  // Toggle eval flag.
  FLAG_EVAL ^= 'true
goto do_fi1

do_come_from:
from main_loop
if COMES = 'ENTRY goto do_entry else do_come_from1

do_come_from1:
from do_come_from
  COMES_TYPE ^= hd COMES
if COMES_TYPE = 'FROM goto do_from else do_fi

do_entry:
from do_come_from
  // nothing to do
goto done_come_from

do_from:
from do_come_from1
  assert(COMES_TYPE = 'FROM)
  assert(PREV_LABEL = tl COMES)

  // Clear label of previous block.
  PREV_LABEL ^= tl COMES
goto done_come_from1

// Evaluate conditional expression of fi
do_fi:
from do_come_from1
  assert(COMES_TYPE = 'FI)
  assert(EXPR = 'nil) 
  EXPR ^= hd (tl COMES)
goto do_eval_fi

do_fi1:
from done_eval_fi
  // Either we have just evaluated EXPR, or we have just unevaluated it.
  // If FLAG_EVAL is true we have just evaluated EXPR, and we use EXPR_RES to decide the branch.
  // If FLAG_EVAL is false we instead go directly to do_if4.
if FLAG_EVAL goto do_fi2 else do_fi4

do_fi2:
from do_fi1
if EXPR_RES goto do_fi_true else do_fi_false

// True case of fi-come-from
do_fi_true:
from do_fi2
  // Clear label of previous block.
  PREV_LABEL ^= hd (tl (tl COMES))
goto do_fi3
  
// False case of fi-come-from
do_fi_false:
from do_fi2
  // Clear label of previous block.
  PREV_LABEL ^= tl (tl (tl COMES))
goto do_fi3

do_fi3:
fi EXPR_RES from do_fi_true else do_fi_false
goto do_fi4

// After unevaluating EXPR, continue to execute the steps of the block
do_fi4:
fi FLAG_EVAL from do_fi3 else do_fi1
  // If FLAG_EVAL is true we unevaluate EXPR.
  // Otherwise we are done with the comes-from.
if FLAG_EVAL goto do_eval_fi else done_fi

// Cleanup after fi comes-from
done_fi:
from do_fi4
  EXPR ^= hd (tl COMES)
  assert(EXPR = 'nil)
goto done_come_from1

// Junction of `do_from` and `done_fi`
done_come_from1:
fi COMES_TYPE = 'FROM from do_from else done_fi
  COMES_TYPE ^= hd COMES
goto done_come_from

// Junction of `do_entry` and `done_come_from1`
done_come_from:
fi COMES = 'ENTRY from do_entry else done_come_from1
goto do_steps

do_steps:
fi SPETS from done_step else done_come_from
if STEPS goto do_steps1 else done_steps

do_steps1:
from do_steps
  (STEP . STEPS) <- STEPS
goto do_step

do_step:
from do_steps1
//if STEP = 'SKIP goto do_skip else do_step1
goto do_skip

// nothing to do
do_skip:
from do_step
goto done_step

done_step:
from do_skip
  SPETS <- (STEP . SPETS)
goto do_steps

done_steps:
fi STEPS from done_steps1 else do_steps
if SPETS goto done_steps1 else do_jump

// Restore SPETS back to STEPS
done_steps1:
from done_steps
  (STEP . SPETS) <- SPETS
  STEPS <- (STEP . STEPS)
goto done_steps

do_jump:
from done_steps
if JUMP = 'EXIT goto do_exit else do_jump1

do_jump1:
from do_jump
  JUMP_TYPE ^= hd JUMP
if JUMP_TYPE = 'GOTO goto do_goto else do_if

do_exit:
from do_jump
  // nothing to do
goto stop

do_goto:
from do_jump1
  assert(JUMP_TYPE = 'GOTO)
  assert(LABEL_TO_FIND = 'nil)

  // save label of new block to find
  LABEL_TO_FIND ^= tl JUMP
goto done_jump

// Evaluate condition expression of if
do_if:
from do_jump1
  assert(JUMP_TYPE = 'IF)
  assert(EXPR = 'nil)
  EXPR ^= hd (tl JUMP)
goto do_eval_if

do_if1:
from done_eval_if
  // Either we have just evaluated EXPR, or we have just unevaluated it.
  // If FLAG_EVAL is true we have just evaluated EXPR, and we use EXPR_RES to decide the branch.
  // If FLAG_EVAL is false we instead go directly to do_if4.
if FLAG_EVAL goto do_if2 else do_if4

do_if2:
from do_if1
if EXPR_RES goto do_if_true else do_if_false

// True case of if-jump
do_if_true:
from do_if2
  // save label of new block to find
  LABEL_TO_FIND ^= hd (tl (tl JUMP))
goto do_if3

// False case of if-jump
do_if_false:
from do_if2
  // save label of new block to find
  LABEL_TO_FIND ^= tl (tl (tl JUMP))
goto do_if3

do_if3:
fi EXPR_RES from do_if_true else do_if_false
goto do_if4

do_if4:
fi FLAG_EVAL from do_if3 else do_if1
  // If FLAG_EVAL is true we unevaluate EXPR.
  // Otherwise we are done with the jump.
if FLAG_EVAL goto do_eval_if else done_if

// Cleanup after if jump
done_if:
from do_if4
  EXPR ^= hd (tl JUMP)
  assert(EXPR = 'nil)
goto done_jump

// Junction of `do_goto` and `done_if`
done_jump:
fi JUMP_TYPE = 'GOTO from do_goto else done_if
  JUMP_TYPE ^= hd JUMP
goto restore_block

// put current block to the head of `BLOCKS`.
// then restore blocks from `SKCOLB` back to `BLOCKS`
restore_block:
from done_jump
  // save copy of `LABEL`
  // will be cleared later from next blocks `from`
  PREV_LABEL ^= LABEL

  BLOCK <- (LABEL . (COMES . (STEPS . JUMP)))
goto restore_block1

// loop test
restore_block1:
fi hd BLOCK = PREV_LABEL from restore_block else restore_block2
  BLOCKS <- (BLOCK . BLOCKS)
if SKCOLB goto restore_block2 else find_block

// loop body
restore_block2:
from restore_block1
  (BLOCK . SKCOLB) <- SKCOLB
goto restore_block1

// find next block to execute
// loops until it finds a block with label = LABEL_TO_FIND.
find_block:
fi SKCOLB from find_block1 else restore_block1
  (BLOCK . BLOCKS) <- BLOCKS
if hd BLOCK = LABEL_TO_FIND goto find_block2 else find_block1

// if the block is not the one we are looking for,
// out it in the SKCOLB list.
find_block1:
from find_block
  SKCOLB <- (BLOCK . SKCOLB)
goto find_block

// case where we found the block
find_block2:
from find_block
  (LABEL . (COMES . (STEPS . JUMP))) <- BLOCK
  LABEL_TO_FIND ^= LABEL
goto main_loop

stop:
from do_exit
  // here we clean up before exiting.
  // we know that the current block is the exit block,
  // and so it belongs at the end of BLOCKS.
  // we also know that all other blocks must be in SKCOLB.
  assert(JUMP = 'EXIT)
  assert(BLOCKS = 'nil)
  // put exit block at from of SKCOLB before moving
  // all blocks from SKCOLB to BLOCKS.
  BLOCK <- (LABEL . (COMES . (STEPS . JUMP)))
  SKCOLB <- (BLOCK . SKCOLB)
goto stop1

// cleanup loop body
stop1:
fi BLOCKS from stop1 else stop
  (BLOCK . SKCOLB) <- SKCOLB
  BLOCKS <- (BLOCK . BLOCKS)
if SKCOLB goto stop1 else stop2

stop2:
from stop1
  prog <- BLOCKS
  output <- STORE
exit
