(prog input)
->
(prog output trace)
with
(BLOCK STEP STEP_TYPE EXPR EXPR_TYPE EXPR_RES COMES_TYPE JUMP_TYPE PREV_LABEL FLAG FLAG_EVAL LABEL COMES STEPS SPETS JUMP BLOCKS SKCOLB STORE EROTS LABEL_TO_FIND VAR_TO_FIND UPDATE_TYPE UPDATE_VAR LOOKUP VAR VAL trace_TMP)

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
// - FLAG: Value used to know where to jump to / come from when jumping to the same block from many sources.
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

// lookup variable of expression
do_lookup_eval:
from eval_var
  assert(VAR_TO_FIND = 'nil)
  VAR_TO_FIND ^= tl EXPR
  FLAG <- ('EVAL . FLAG)
goto do_lookup

// lookup variable of update step
do_lookup_update:
from do_update2
  assert(VAR_TO_FIND = 'nil)
  VAR_TO_FIND ^= hd (tl (tl STEP))
  FLAG <- ('UPDATE . FLAG)
goto do_lookup

// Look up VAR_TO_FIND,
// storing the resulting variable/value pair in LOOKUP.
do_lookup:
fi hd FLAG = 'EVAL from do_lookup_eval else do_lookup_update
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
if hd FLAG = 'EVAL goto done_lookup_eval else done_lookup_update

// return to update step after lookup
done_lookup_update:
from done_lookup
  ('UPDATE . FLAG) <- FLAG
  VAR_TO_FIND ^= hd (tl (tl STEP))
  assert(VAR_TO_FIND = 'nil)
goto do_update3

// return to evaluating variable expression after lookup
done_lookup_eval:
from done_lookup
  ('EVAL . FLAG) <- FLAG
  VAR_TO_FIND ^= tl EXPR
  assert(VAR_TO_FIND = 'nil)
goto eval_var1

// undo lookup variable of expression
undo_lookup_eval:
from eval_var1
  assert(VAR_TO_FIND = 'nil)
  VAR_TO_FIND ^= tl EXPR
  FLAG <- ('EVAL . FLAG)
goto undo_lookup

// undo lookup variable of update step
undo_lookup_update:
from done_update3
  assert(VAR_TO_FIND = 'nil)
  VAR_TO_FIND ^= UPDATE_VAR
  FLAG <- ('UPDATE . FLAG)
goto undo_lookup

// Restore LOOKUP back to store and EROTS back to STORE.
undo_lookup:
fi hd FLAG = 'EVAL from undo_lookup_eval else undo_lookup_update
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
if hd FLAG = 'EVAL goto undone_lookup_eval else undone_lookup_update

// return to update step after undoing lookup
undone_lookup_update:
from undone_lookup
  ('UPDATE . FLAG) <- FLAG
  VAR_TO_FIND ^= UPDATE_VAR
  assert(VAR_TO_FIND = 'nil)
goto done_update2

// return to evaluating variable expression after undoing lookup
undone_lookup_eval:
from undone_lookup
  ('EVAL . FLAG) <- FLAG
  VAR_TO_FIND ^= tl EXPR
  assert(VAR_TO_FIND = 'nil)
goto eval_var2

// evaluate expression of "if" jump
do_eval_if:
fi FLAG_EVAL from do_if4 else do_if 
  FLAG <- ('IF . FLAG)
goto do_eval_junction

// evaluate expression of "fi" come-from
do_eval_fi:
fi FLAG_EVAL from do_fi4 else do_fi 
  FLAG <- ('FI . FLAG)
goto do_eval_junction

// evaluate expression of "update" step
do_eval_update:
fi FLAG_EVAL from done_update1 else do_update 
  FLAG <- ('UPDATE . FLAG)
goto do_eval_junction1

// junction block
do_eval_junction:
fi hd FLAG = 'IF from do_eval_if else do_eval_fi
goto do_eval_junction1

// junction block
do_eval_junction1:
fi hd FLAG = 'UPDATE from do_eval_update else do_eval_junction
goto do_eval

// Evaluate the expression in EXPR,
// and store the result in EXPR_RES.
do_eval:
from do_eval_junction1
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
goto do_lookup_eval

eval_var1:
from done_lookup_eval
  EXPR_RES ^= tl LOOKUP
goto undo_lookup_eval

eval_var2:
from undone_lookup_eval
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
goto done_eval_junction1

// junction block
done_eval_junction1:
from done_eval
if hd FLAG = 'UPDATE goto done_eval_update else done_eval_junction

// junction block
done_eval_junction:
from done_eval_junction1
if hd FLAG = 'IF goto done_eval_if else done_eval_fi

done_eval_update:
from done_eval_junction1
  assert(hd FLAG = 'UPDATE)
  ('UPDATE . FLAG) <- FLAG
  // Toggle eval flag.
  FLAG_EVAL ^= 'true
goto do_update1

done_eval_if:
from done_eval_junction
  assert(hd FLAG = 'IF)
  ('IF . FLAG) <- FLAG
  // Toggle eval flag.
  FLAG_EVAL ^= 'true
goto do_if1

done_eval_fi:
from done_eval_junction
  assert(hd FLAG = 'FI)
  ('FI . FLAG) <- FLAG
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
if STEPS goto do_steps_loop else done_steps

do_steps_loop:
from do_steps
  (STEP . STEPS) <- STEPS
goto do_step

do_step:
from do_steps_loop
if STEP = 'SKIP goto do_skip else do_step1

do_step1:
from do_step
  STEP_TYPE ^= hd STEP
if STEP_TYPE = 'ASSERT goto do_assert else do_step2

do_step2:
from do_step1
if STEP_TYPE = 'REPLACE goto do_replace else do_step3

do_step3:
from do_step2
  assert(STEP_TYPE = 'UPDATE)
goto do_update

// nothing to do
do_skip:
from do_step
goto done_step

do_assert:
from do_step1
  // TODO: implement assert
  assert(!'not_implemented)
goto done_step1

do_replace:
from do_step2
  // TODO: implement replace
  assert(!'not_implemented)
goto done_step2

do_update:
from do_step3
  assert(EXPR        = 'nil)
  assert(UPDATE_VAR  = 'nil)
  assert(UPDATE_TYPE = 'nil)
  UPDATE_TYPE ^= hd (tl STEP)
  UPDATE_VAR ^= hd (tl (tl STEP))
  EXPR ^= tl (tl (tl STEP))
goto do_eval_update

do_update1:
from done_eval_update
  // Either we have just evaluated EXPR, or we have just unevaluated it.
  // If FLAG_EVAL is true we have just evaluated EXPR,
  //   so we lookup the variable and update it.
  // If FLAG_EVAL is false we instead go directly to do_update?.
if FLAG_EVAL goto do_update2 else done_update1

do_update2:
from do_update1
goto do_lookup_update

do_update3:
from done_lookup_update
  (VAR . VAL) <- LOOKUP
if UPDATE_TYPE = 'ADD goto do_update_add else do_update4

do_update4:
from do_update3
if UPDATE_TYPE = 'SUB goto do_update_sub else do_update5

do_update5:
from do_update4
  assert(UPDATE_TYPE = 'XOR)
goto do_update_xor

do_update_add:
from do_update3
  VAL += EXPR_RES
goto done_update3

do_update_sub:
from do_update4
  VAL -= EXPR_RES
goto done_update4

do_update_xor:
from do_update5
  VAL ^= EXPR_RES
goto done_update5

done_update5:
from do_update_xor
goto done_update4

done_update4:
fi UPDATE_TYPE = 'SUB from do_update_sub else done_update5
goto done_update3

done_update3:
fi UPDATE_TYPE = 'ADD from do_update_add else done_update4
  LOOKUP <- (VAR . VAL)
goto undo_lookup_update

done_update2:
from undone_lookup_update
goto done_update1

done_update1:
fi FLAG_EVAL from done_update2 else do_update1
  // If FLAG_EVAL is true we unevaluate EXPR.
  // Otherwise we are done with the update step.
if FLAG_EVAL goto do_eval_update else done_update

done_update:
from done_update1
  UPDATE_TYPE ^= hd (tl STEP)
  UPDATE_VAR ^= hd (tl (tl STEP))
  EXPR ^= tl (tl (tl STEP))
  assert(EXPR        = 'nil)
  assert(UPDATE_VAR  = 'nil)
  assert(UPDATE_TYPE = 'nil)
goto done_step3

done_step3:
from done_update
  assert(STEP_TYPE = 'UPDATE)
goto done_step2

done_step2:
fi STEP_TYPE = 'REPLACE from do_replace else done_step3
goto done_step1

done_step1:
fi STEP_TYPE = 'ASSERT from do_assert else done_step2
  STEP_TYPE ^= hd STEP
goto done_step

done_step:
fi STEP = 'SKIP from do_skip else done_step1
  SPETS <- (STEP . SPETS)
goto do_steps

done_steps:
fi STEPS from done_steps_loop else do_steps
if SPETS goto done_steps_loop else do_jump

// Restore SPETS back to STEPS
done_steps_loop:
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
