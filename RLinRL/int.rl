(prog input)
->
(prog output)
with
(STORE BLOCK LABEL COMES STEPS JUMP BLOCKS STEP STEP_TYPE
 COMES_TYPE JUMP_TYPE UPDATE_TYPE EXPR EXPR_TYPE
 PREV_LABEL UPDATE_VAR LOOKUP VAR VAL OP LABEL_TO_FIND VAR_TO_FIND STACK TMP
 FLAG FLAG_EVAL RES EXPR_L EXPR_R RES_L RES_R
 SPETS SKCOLB EROTS)

// NOTE: Many of these variables will often be 'nil, e.g. `BLOCK` is described
// as the current block, but often it will have been destructed to
// `LABEL`, `COMES`, `STEPS` and `JUMP`.
// 
// When traversing a list of elements, we need another list to store the
// elements we have passed. I name these variables the reverse of the original,
// e.g. `EROTS` holds the part of `STORE` which is passed over when doing a
// lookup.
// 
// Meanings of variables:
// - prog: Program to interpret
// - input: Initial store
// - output: Final store
// - STORE / EROTS: Current store, save for `LOOKUP`
// - BLOCK: Current block
// - LABEL: Current label
// - COMES: Current comes-from
// - STEPS / SPETS: Steps of current block, save for `STEP`
// - JUMP: Current jump
// - BLOCKS / SKCOLB: All blocks except for `BLOCK`
// - STEP: Current step to perform
// - STEP_TYPE: Type of current step
// - COMES_TYPE: Type of current comes-from
// - JUMP_TYPE: Type of current jump
// - UPDATE_TYPE: Type of current update
// - UPDATE_VAR: Name of variable to update
// - EXPR: Expression to be evaluated / unevaluated
// - EXPR_TYPE: Type of expression
// - PREV_LABEL: Label of previos block
// - LOOKUP: Where result of `do_lookup` is stored
// - VAR: Variable part of `LOOKUP`
// - VAL: Value part of `LOOKUP`
// - LABEL_TO_FIND: Next label to jump to
// - VAR_TO_FIND: Target of `do_lookup`
// - OP: Operator to evaluate
// - RES: Where result of `do_eval` is stored
// - EXPR_L: Left sub-expression of binary operator
// - EXPR_R: Right sub-expression of binary operator
// - RES_L: Result of left sub-expression
// - RES_R: Result of right sub-expression
// - FLAG: Used to determine from which block we came from and where to go
// - FLAG_EVAL: Set to true if expression has been evaluated.
//              Set to false after expression has been unevaluated.
// - STACK: Used to store "local variables" when simulating recursive calls.
// - TMP: General purpouse temporary variable.

init:
entry
  // Preprocessed programs always have the entry block first
  (BLOCK . BLOCKS) <- prog
  (LABEL . (COMES . (STEPS . JUMP))) <- BLOCK
  STORE <- input
goto main_loop

// MAIN LOOP
// =========
// Processes the current block in order: come from -> steps -> jump -> new block
main_loop:
fi COMES = 'ENTRY from init else find_block2
goto do_come_from

// COME FROM
// ---------
// Use come-from of current block to clear `PREV_LABEL`
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
  // If FLAG_EVAL is true we have just evaluated EXPR,
  // and we use RES to decide the branch.
  // If FLAG_EVAL is false we instead go directly to do_if4.
if FLAG_EVAL goto do_fi2 else do_fi4

do_fi2:
from do_fi1
if RES goto do_fi_true else do_fi_false

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
fi RES from do_fi_true else do_fi_false
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

// STEPS
// -----
// Loop over and execute each step of the current block
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
  assert(EXPR = 'nil)
  EXPR ^= tl STEP
goto do_eval_assert

do_assert1:
from done_eval_assert
  // Either we have just evaluated EXPR, or we have just unevaluated it.
  // If FLAG_EVAL is true we have just evaluated EXPR,
  //   so we assert the result.
  // If FLAG_EVAL is false we instead go directly to done_assert1.
if FLAG_EVAL goto do_assert2 else done_assert1

do_assert2:
from do_assert1
  assert(RES)
goto done_assert2

done_assert2:
from do_assert2
goto done_assert1

done_assert1:
fi FLAG_EVAL from done_assert2 else do_assert1
  // If FLAG_EVAL is true we unevaluate EXPR.
  // Otherwise we are done with the assert step.
if FLAG_EVAL goto do_eval_assert else done_assert

done_assert:
from done_assert1
  EXPR ^= tl (STEP)
  assert(EXPR = 'nil)
goto done_step1

do_replace:
from do_step2
  // TODO: implement replace
  assert(!'replace_not_implemented)
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
  // If FLAG_EVAL is false we instead go directly to done_update1.
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
  VAL += RES
goto done_update3

do_update_sub:
from do_update4
  VAL -= RES
goto done_update4

do_update_xor:
from do_update5
  VAL ^= RES
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
fi STEP_TYPE = 'ASSERT from done_assert else done_step2
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

// JUMP
// ----
// Find label of next block, restore current block to `BLOCKS`,
// and find next block.
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
  // If FLAG_EVAL is true we have just evaluated EXPR, and we use RES to decide the branch.
  // If FLAG_EVAL is false we instead go directly to do_if4.
if FLAG_EVAL goto do_if2 else do_if4

do_if2:
from do_if1
if RES goto do_if_true else do_if_false

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
fi RES from do_if_true else do_if_false
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

// RESTORING BLOCKS
// ----------------
// put current block to the head of `BLOCKS`.
// then restore blocks from `SKCOLB` back to `BLOCKS`
restore_block:
from done_jump
  // save copy of `LABEL`
  // will be cleared later from next blocks `from`
  PREV_LABEL ^= LABEL

  BLOCK <- (LABEL . (COMES . (STEPS . JUMP)))
goto restore_block1

restore_block1:
fi hd BLOCK = PREV_LABEL from restore_block else restore_block2
  BLOCKS <- (BLOCK . BLOCKS)
if SKCOLB goto restore_block2 else find_block

restore_block2:
from restore_block1
  (BLOCK . SKCOLB) <- SKCOLB
goto restore_block1

// FINDING NEXT BLOCK
// ------------------
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

// END OF MAIN LOOP
// ================

// CLEANUP
// -------
// Clean up after exit block has been executed.
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

// VARIABLE LOOKUP
// ===============

// DO VARIABLE LOOKUP
// ------------------

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

// UNDO VARIABLE LOOKUP
// --------------------

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

// EVALUATE EXPRESSION
// ===================

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

// evaluate operand of a unary operator
do_eval_operand:
fi FLAG_EVAL from done_eval_unop1 else do_eval_unop
  FLAG <- ('OPERAND . FLAG)
goto do_eval_junction2

// evaluate left operand of a binary operator
do_eval_operand_left:
fi FLAG_EVAL from done_eval_binop1 else do_eval_binop
  FLAG <- ('OPERAND_L . FLAG)
goto do_eval_junction3

// evaluate right operand of a binary operator
do_eval_operand_right:
fi FLAG_EVAL from done_eval_binop3 else do_eval_binop2
  FLAG <- ('OPERAND_R . FLAG)
goto do_eval_junction4

// evaluate expression of assertion
do_eval_assert:
fi FLAG_EVAL from done_assert1 else do_assert
  FLAG <- ('ASSERT . FLAG)
goto do_eval_junction5

do_eval_junction:
fi hd FLAG = 'IF from do_eval_if else do_eval_fi
goto do_eval_junction1

do_eval_junction1:
fi hd FLAG = 'UPDATE from do_eval_update else do_eval_junction
goto do_eval_junction2

do_eval_junction2:
fi hd FLAG = 'OPERAND from do_eval_operand else do_eval_junction1
goto do_eval_junction3

do_eval_junction3:
fi hd FLAG = 'OPERAND_L from do_eval_operand_left else do_eval_junction2
goto do_eval_junction4

do_eval_junction4:
fi hd FLAG = 'OPERAND_R from do_eval_operand_right else do_eval_junction3
goto do_eval_junction5

do_eval_junction5:
fi hd FLAG = 'ASSERT from do_eval_assert else do_eval_junction4
goto do_eval

// Evaluate the expression in EXPR,
// and store the result in RES.
do_eval:
from do_eval_junction5
  assert(EXPR_TYPE = 'nil)
  EXPR_TYPE ^= hd EXPR
if EXPR_TYPE = 'CONST goto eval_const else do_eval1

do_eval1:
from do_eval
if EXPR_TYPE = 'VAR goto eval_var else do_eval2

do_eval2:
from do_eval1
if EXPR_TYPE = 'UNOP goto do_eval_unop else do_eval3

do_eval3:
from do_eval2
  assert(EXPR_TYPE = 'BINOP)
goto do_eval_binop

// Evaluate a constant
eval_const:
from do_eval
  assert(EXPR_TYPE = 'CONST)
  RES ^= tl EXPR
goto done_eval

// Evaluate a variable
eval_var:
from do_eval1
  assert(EXPR_TYPE = 'VAR)
goto do_lookup_eval

eval_var1:
from done_lookup_eval
  RES ^= tl LOOKUP
goto undo_lookup_eval

eval_var2:
from undone_lookup_eval
goto done_eval1

// Evaluate unary operator
do_eval_unop:
from do_eval2
  EXPR_TYPE ^= 'UNOP
  // Extract operator and inner expression
  (EXPR_TYPE . (OP . EXPR)) <- EXPR

  // temporarily clear expression type
  EXPR_TYPE ^= 'UNOP

  // we might be unevaluating this expression,
  // but locally we wan't it to look like we are evaluating it,
  // so we put the flag on the stack
  STACK <- (FLAG_EVAL . STACK)

  // also save the current expression result on the stack,
  // so that in case we are unevaluating it we can still evaluate the sub-expression
  STACK <- (RES . STACK)

  // finally, save the operator on the stack in case it is used by sub-expressions
  STACK <- (OP . STACK)
// Recursively evaluate inner sub-expression
goto do_eval_operand

do_eval_unop1:
from done_eval_operand
  // Either we have just evaluated EXPR, or we have just unevaluated it.
  // If FLAG_EVAL is true we have just evaluated EXPR, and we evaluate the unop
  // If FLAG_EVAL is false we instead go directly to done_eval_unop1.
if FLAG_EVAL goto do_eval_unop2 else done_eval_unop1

// Look at operator and apply it to RES,
// storing the result (temporarily) in TMP
do_eval_unop2:
from do_eval_unop1
  (OP . STACK) <- STACK

  // The result will be stored in TMP,
  // so make sure it is clear
  assert(TMP = 'nil)
  (TMP . STACK) <- STACK
if OP = 'NOT goto eval_not else do_eval_unop3

do_eval_unop3:
from do_eval_unop2
if OP = 'HD goto eval_hd else do_eval_unop4

do_eval_unop4:
from do_eval_unop3
  assert(OP = 'TL)
goto eval_tl

// Evaluate NOT expression, storing the result in TMP
eval_not:
from do_eval_unop2
  TMP ^= ! RES
goto done_eval_unop2

// Evaluate HD (head) expression, storing the result in TMP
eval_hd:
from do_eval_unop3
  TMP ^= hd RES
goto done_eval_unop3

// Evaluate TL (tail) expression, storing the result in TMP
eval_tl:
from do_eval_unop4
  TMP ^= tl RES
goto done_eval_unop4

done_eval_unop4:
from eval_tl
  assert(OP = 'TL)
goto done_eval_unop3

done_eval_unop3:
fi OP = 'HD from eval_hd else done_eval_unop4
goto done_eval_unop2

done_eval_unop2:
fi OP = 'NOT from eval_not else done_eval_unop3
  // put result on the stack
  STACK <- (TMP . STACK)
  // put operator back on the stack
  STACK <- (OP . STACK)
goto done_eval_unop1

// Unevaluate operand of unary expression
done_eval_unop1:
fi FLAG_EVAL from done_eval_unop2 else do_eval_unop1
  // If FLAG_EVAL is true we unevaluate EXPR.
  // Otherwise we have already unevaluated it, so we continue.
if FLAG_EVAL goto do_eval_operand else done_eval_unop

done_eval_unop:
from done_eval_unop1
  // Restore original expression
  EXPR_TYPE ^= 'UNOP
  (OP . STACK) <- STACK
  EXPR <- (EXPR_TYPE . (OP . EXPR))

  // Restore expression type
  EXPR_TYPE ^= 'UNOP

  // Save result
  (RES . STACK) <- STACK

  // restore old eval flag
  (FLAG_EVAL . STACK) <- STACK
goto done_eval2

// Evaluate binary operator
do_eval_binop:
from do_eval3
  EXPR_TYPE ^= 'BINOP
  // Extract operator and inner expressions
  (EXPR_TYPE . (OP . (EXPR_L . EXPR_R))) <- EXPR

  // clear expression type while evaluating inner expressions
  EXPR_TYPE ^= 'BINOP

  // we might be unevaluating this expression,
  // but locally we wan't it to look like we are evaluating it,
  // so we put the flag on the stack
  STACK <- (FLAG_EVAL . STACK)

  // initially evaluate left sub-expression
  EXPR ^= EXPR_L
  // and save the sub-expressions on the stack
  STACK <- ((EXPR_L . EXPR_R) . STACK)

  // also save the current expression result on the stack,
  // so that in case we are unevaluating it we can
  // still evaluate the sub-expression
  STACK <- (RES . STACK)

  // finally, save the operator on the stack in case it
  // is used by sub-expressions
  STACK <- (OP . STACK)
// Recursively evaluate left sub-expression
goto do_eval_operand_left

do_eval_binop1:
from done_eval_operand_left
  // Either we have just evaluated EXPR_L, or we have just unevaluated it.
  // If FLAG_EVAL is true we have just evaluated the left sub-expression,
  // and we then evaluate the right sub-expression.
  // If FLAG_EVAL is false we instead go directly to done_eval_binop1.
if FLAG_EVAL goto do_eval_binop2 else done_eval_binop1

do_eval_binop2:
from do_eval_binop1
  // As we have just evaluated the left sub-expression,
  // FLAG_EVAL will be true, so we toggle it so that evaluating
  // the right sub-expression will turn it on again.
  assert(FLAG_EVAL)
  FLAG_EVAL ^= 'true

  // Pop the left- and right sub-expressions from the stack
  (OP . STACK) <- STACK
  (TMP . STACK) <- STACK
  ((EXPR_L . EXPR_R) . STACK) <- STACK

  // Switch EXPR from the left sub-expression to the right
  EXPR ^= EXPR_L
  EXPR ^= EXPR_R

  // Restore the stack
  STACK <- ((EXPR_L . EXPR_R) . STACK)
  STACK <- (TMP . STACK)
  STACK <- (OP . STACK)

  // We have just evaluated the left sub-expression,
  // so we store the result on the stack and evaluate the right sub-expression
  RES_L <- RES
  STACK <- (RES_L . STACK)
// Recursively evaluate right sub-expression
goto do_eval_operand_right

do_eval_binop3:
from done_eval_operand_right
  // Either we have just evaluated EXPR_R, or we have just unevaluated it.
  // If FLAG_EVAL is true we have just evaluated the right sub-expression,
  // and we then evaluate the binop.
  // If FLAG_EVAL is false we instead go directly to done_eval_binop3
if FLAG_EVAL goto do_eval_binop4 else done_eval_binop3

// Look at operator and apply it to the left and right sub-expressions,
// storing the result (temporarily) in TMP
do_eval_binop4:
from do_eval_binop3
  RES_R <- RES
  (RES_L . STACK) <- STACK
  (OP . STACK) <- STACK

  // The result will be stored in TMP,
  // so make sure it is clear
  assert(TMP = 'nil)
  (TMP . STACK) <- STACK
goto do_eval_binop5

do_eval_binop5:
from do_eval_binop4
if OP = 'CONS goto eval_cons else do_eval_binop6

do_eval_binop6:
from do_eval_binop5
if OP = 'AND goto eval_and else do_eval_binop7

do_eval_binop7:
from do_eval_binop6
if OP = 'OR goto eval_or else do_eval_binop8

do_eval_binop8:
from do_eval_binop7
if OP = 'LESS goto eval_less else do_eval_binop9

do_eval_binop9:
from do_eval_binop8
if OP = 'GREATER goto eval_greater else do_eval_binop10

do_eval_binop10:
from do_eval_binop9
if OP = 'EQUAL goto eval_equal else do_eval_binop11

do_eval_binop11:
from do_eval_binop10
if OP = 'ADD goto eval_add else do_eval_binop12

do_eval_binop12:
from do_eval_binop11
if OP = 'SUB goto eval_sub else do_eval_binop13

do_eval_binop13:
from do_eval_binop12
if OP = 'MUL goto eval_mul else do_eval_binop14

do_eval_binop14:
from do_eval_binop13
if OP = 'DIV goto eval_div else do_eval_binop15

do_eval_binop15:
from do_eval_binop14
  assert(OP = 'XOR)
goto eval_xor

eval_cons:
from do_eval_binop5
  TMP ^= (RES_L . RES_R)
goto done_eval_binop5

eval_and:
from do_eval_binop6
  TMP ^= RES_L && RES_R
goto done_eval_binop6

eval_or:
from do_eval_binop7
  TMP ^= RES_L || RES_R
goto done_eval_binop7

eval_less:
from do_eval_binop8
  TMP ^= RES_L < RES_R
goto done_eval_binop8

eval_greater:
from do_eval_binop9
  TMP ^= RES_L > RES_R
goto done_eval_binop9

eval_equal:
from do_eval_binop10
  TMP ^= RES_L = RES_R
goto done_eval_binop10

eval_add:
from do_eval_binop11
  TMP ^= RES_L + RES_R
goto done_eval_binop11

eval_sub:
from do_eval_binop12
  TMP ^= RES_L - RES_R
goto done_eval_binop12

eval_mul:
from do_eval_binop13
  TMP ^= RES_L * RES_R
goto done_eval_binop13

eval_div:
from do_eval_binop14
  TMP ^= RES_L / RES_R
goto done_eval_binop14

eval_xor:
from do_eval_binop15
  TMP ^= RES_L ^ RES_R
goto done_eval_binop15

done_eval_binop15:
from eval_xor
  assert(OP = 'XOR)
goto done_eval_binop14

done_eval_binop14:
fi OP = 'DIV from eval_div else done_eval_binop15
goto done_eval_binop13

done_eval_binop13:
fi OP = 'MUL from eval_mul else done_eval_binop14
goto done_eval_binop12

done_eval_binop12:
fi OP = 'SUB from eval_sub else done_eval_binop13
goto done_eval_binop11

done_eval_binop11:
fi OP = 'ADD from eval_add else done_eval_binop12
goto done_eval_binop10

done_eval_binop10:
fi OP = 'EQUAL from eval_equal else done_eval_binop11
goto done_eval_binop9

done_eval_binop9:
fi OP = 'GREATER from eval_greater else done_eval_binop10
goto done_eval_binop8

done_eval_binop8:
fi OP = 'LESS from eval_less else done_eval_binop9
goto done_eval_binop7

done_eval_binop7:
fi OP = 'OR from eval_or else done_eval_binop8
goto done_eval_binop6

done_eval_binop6:
fi OP = 'AND from eval_and else done_eval_binop7
goto done_eval_binop5

done_eval_binop5:
fi OP = 'CONS from eval_cons else done_eval_binop6
goto done_eval_binop4

done_eval_binop4:
from done_eval_binop5
  // put result on the stack
  STACK <- (TMP . STACK)
  // put operator back on the stack
  STACK <- (OP . STACK)
  // put result of left sub-expression on stack
  STACK <- (RES_L . STACK)
  // prepare to unevaluate right sub-expression
  RES <- RES_R
goto done_eval_binop3

// Unevaluate right sub-expression
done_eval_binop3:
fi FLAG_EVAL from done_eval_binop4 else do_eval_binop3
  // If FLAG_EVAL is true we unevaluate the right sub-expression.
  // Otherwise we have already unevaluated it, so we continue.
if FLAG_EVAL goto do_eval_operand_right else done_eval_binop2

done_eval_binop2:
from done_eval_binop3
  // As we have just unevaluated the right sub-expression,
  // FLAG_EVAL will be false, so we toggle it so that evaluating
  // the left sub-expression will turn it off.
  assert(! FLAG_EVAL)
  FLAG_EVAL ^= 'true

  // pop result of left sub-expression from stack
  (RES_L . STACK) <- STACK
  // Pop the left- and right sub-expressions from the stack
  (OP . STACK) <- STACK
  (TMP . STACK) <- STACK
  ((EXPR_L . EXPR_R) . STACK) <- STACK

  // Switch EXPR from the right sub-expression to the left
  EXPR ^= EXPR_R
  EXPR ^= EXPR_L

  // Restore the stack
  STACK <- ((EXPR_L . EXPR_R) . STACK)
  STACK <- (TMP . STACK)
  STACK <- (OP . STACK)

  // prepare to unevaluate left sub-expression
  RES <- RES_L
goto done_eval_binop1

// Unevaluate left sub-expression
done_eval_binop1:
fi FLAG_EVAL from done_eval_binop2 else do_eval_binop1
  // If FLAG_EVAL is true we unevaluate the left sub-expression.
  // Otherwise we have already unevaluated it, so we continue.
if FLAG_EVAL goto do_eval_operand_left else done_eval_binop

done_eval_binop:
from done_eval_binop1
  // Save result
  (OP . STACK) <- STACK
  (RES . STACK) <- STACK

  // Restore original expression
  EXPR_TYPE ^= 'BINOP
  ((EXPR_L . EXPR_R) . STACK) <- STACK
  EXPR ^= EXPR_L
  EXPR <- (EXPR_TYPE . (OP . (EXPR_L . EXPR_R)))

  // Restore expression type
  EXPR_TYPE ^= 'BINOP

  // restore old eval flag
  (FLAG_EVAL . STACK) <- STACK
goto done_eval3

done_eval3:
from done_eval_binop
  assert(EXPR_TYPE = 'BINOP)
goto done_eval2

done_eval2:
fi EXPR_TYPE = 'UNOP from done_eval_unop else done_eval3
goto done_eval1

done_eval1:
fi EXPR_TYPE = 'VAR from eval_var2 else done_eval2
goto done_eval

// cleanup after evaluating expression
done_eval:
fi EXPR_TYPE = 'CONST from eval_const else done_eval1
  EXPR_TYPE ^= hd EXPR
goto done_eval_junction5

// junction block
done_eval_junction5:
from done_eval
if hd FLAG = 'ASSERT goto done_eval_assert else done_eval_junction4

// junction block
done_eval_junction4:
from done_eval_junction5
if hd FLAG = 'OPERAND_R goto done_eval_operand_right else done_eval_junction3

// junction block
done_eval_junction3:
from done_eval_junction4
if hd FLAG = 'OPERAND_L goto done_eval_operand_left else done_eval_junction2

// junction block
done_eval_junction2:
from done_eval_junction3
if hd FLAG = 'OPERAND goto done_eval_operand else done_eval_junction1

// junction block
done_eval_junction1:
from done_eval_junction2
if hd FLAG = 'UPDATE goto done_eval_update else done_eval_junction

// junction block
done_eval_junction:
from done_eval_junction1
if hd FLAG = 'IF goto done_eval_if else done_eval_fi

done_eval_assert:
from done_eval_junction5
  assert(hd FLAG = 'ASSERT)
  ('ASSERT . FLAG) <- FLAG
  // Toggle eval flag.
  FLAG_EVAL ^= 'true
goto do_assert1

done_eval_operand_right:
from done_eval_junction4
  assert(hd FLAG = 'OPERAND_R)
  ('OPERAND_R . FLAG) <- FLAG
  // Toggle eval flag.
  FLAG_EVAL ^= 'true
goto do_eval_binop3

done_eval_operand_left:
from done_eval_junction3
  assert(hd FLAG = 'OPERAND_L)
  ('OPERAND_L . FLAG) <- FLAG
  // Toggle eval flag.
  FLAG_EVAL ^= 'true
goto do_eval_binop1

done_eval_operand:
from done_eval_junction2
  assert(hd FLAG = 'OPERAND)
  ('OPERAND . FLAG) <- FLAG
  // Toggle eval flag.
  FLAG_EVAL ^= 'true
goto do_eval_unop1

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
