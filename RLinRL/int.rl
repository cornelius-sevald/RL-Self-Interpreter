(prog input)
->
(BLOCK BLOCKS SKCOLB LABEL FROM STEPS JUMP LABEL_TO_FIND)
with
(FROM_TYPE JUMP_TYPE TMP1 TMP2 I PREV_BLOCK)

// READ:
// Think I should let `SKCOLB` (terrible name) be non-nil,
// right up until I have to find the new block. Then restore it
// onto `BLOCKS` and search.

init:
entry
  // Initialize numeric variables
  LABEL_TO_FIND <- '0
  I <- '0

  // Preprocessed programs always have the entry block first
  (BLOCK . BLOCKS) <- prog
  (LABEL . (FROM . (STEPS . JUMP))) <- BLOCK
goto main_loop

main_loop:
fi FROM = 'ENTRY from init else init // ???
goto do_comes_from

do_comes_from:
from main_loop
if FROM = 'ENTRY goto do_entry else do_comes_from1

do_comes_from1:
from do_comes_from
  (FROM_TYPE . TMP1) <- FROM
  // TODO: implement more comes from
goto do_from

do_entry:
from do_comes_from
  // nothing to do
goto do_steps

do_from:
from do_comes_from1
  assert(TMP1 = PREV_BLOCK)
  PREV_BLOCK -= TMP1

  FROM <- (FROM_TYPE . TMP1)
goto do_steps

do_steps:
fi FROM = 'ENTRY from do_entry else do_from
  // TODO: implement
goto do_jump

do_jump:
from do_steps
if JUMP = 'EXIT goto do_exit else do_jump1

do_jump1:
from do_jump
  (JUMP_TYPE . TMP1) <- JUMP
  // TODO: implement more jump types
goto do_goto

do_exit:
from do_jump
  // nothing to do
goto stop

do_goto:
from do_jump1
  assert(JUMP_TYPE = 'GOTO)
  assert(LABEL_TO_FIND = '0)

  // save index of new block to find
  LABEL_TO_FIND += TMP1
  // restore current block and then find the next one
  'GOTO <- JUMP_TYPE
  JUMP <- (JUMP_TYPE . TMP1)
goto restore_block

// put current block to the head of `BLOCKS`.
// then restore blocks from `SKCOLB` back to `BLOCKS`
restore_block:
from do_goto
  assert(I = '0)
  I += LABEL
  // save copy of `LABEL`
  // will be cleared later from next blocks `from`
  PREV_BLOCK <- '0
  PREV_BLOCK += LABEL

  BLOCK <- (LABEL . (FROM . (STEPS . JUMP)))
  BLOCKS <- (BLOCK . BLOCKS)
goto restore_block1

// loop test
restore_block1:
fi I = PREV_BLOCK from restore_block else restore_block2
if I > '0 goto restore_block2 else restore_block3

// loop body
restore_block2:
from restore_block1
  (BLOCK . SKCOLB) <- SKCOLB
  BLOCKS <- (BLOCK . BLOCKS)
  I -= '1
goto restore_block1

// cleanup
restore_block3:
fi '0 = '0 from restore_block1 else restore_block3
  assert(SKCOLB = 'nil)
  assert('0 = '1)
goto restore_block3

stop:
from do_exit
exit

// OLD
// ===

//// restore current block back into `BLOCKS` at the correct index
//restore_block:
//from do_goto
//  assert(I = '0)
//  // initialize loop counter
//  I += LABEL
//goto restore_block1
//
//// loop test
//restore_block1:
//fi I = LABEL from restore_block else restore_block2
//if I > '0 goto restore_block2 else restore_block3
//
//// loop body
//restore_block2:
//from restore_block1
//  // pop top block off and save it in temporary list
//  (BLOCK . BLOCKS) <- BLOCKS
//  SKCOLB <- (BLOCK . SKCOLB)
//  I -= '1
//goto restore_block1
//
//// current block belongs at head of list
//restore_block3:
//from restore_block1
//  // restore loop counter for putting blocks back
//  assert(I = '0)
//  I += LABEL
//  // also keep a copy of the label
//  assert(TMP1 = 'nil)
//  TMP1 <- '0
//  TMP1 += LABEL
//
//  // put current block at head of list
//  BLOCK <- (LABEL . (FROM . (STEPS . JUMP)))
//  BLOCKS <- (BLOCK . BLOCKS)
//  
//  // then put the blocks in `SKCOLB` back
//goto restore_block4
//
//// loop test
//restore_block4:
//fi I = TMP1 from restore_block3 else restore_block5
//if I > '0 goto restore_block5 else restore_block6
//
//restore_block5:
//from restore_block4
//  // pop top block off temporary list and save it in block list
//  (BLOCK . SKCOLB) <- SKCOLB
//  BLOCKS <- (BLOCK . BLOCKS)
//  I -= '1
//goto restore_block4
//
//// clean up
//restore_block6:
//from restore_block4
//  '0 <- TMP1
//
//// TODO: find new block
//goto get_new_block
