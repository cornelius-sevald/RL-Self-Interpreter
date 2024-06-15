(prog input)
->
(BLOCK BLOCKS SKCOLB LABEL COMES STEPS JUMP LABEL_TO_FIND)
with
(COMES_TYPE JUMP_TYPE PREV_LABEL)

// READ:
// Think I should let `SKCOLB` (terrible name) be non-nil,
// right up until I have to find the new block. Then restore it
// onto `BLOCKS` and search.

init:
entry
  // Preprocessed programs always have the entry block first
  (BLOCK . BLOCKS) <- prog
  (LABEL . (COMES . (STEPS . JUMP))) <- BLOCK
goto main_loop

main_loop:
fi COMES = 'ENTRY from init else find_block2
goto do_comes_from

do_comes_from:
from main_loop
if COMES = 'ENTRY goto do_entry else do_comes_from1

do_comes_from1:
from do_comes_from
  COMES_TYPE ^= hd COMES
  // TODO: implement more comes from
goto do_from

do_entry:
from do_comes_from
  // nothing to do
goto do_steps

do_from:
from do_comes_from1
  assert(COMES_TYPE = 'FROM)
  assert(PREV_LABEL = tl COMES)

  COMES_TYPE ^= 'FROM
  PREV_LABEL ^= tl COMES
goto do_steps

do_steps:
fi COMES = 'ENTRY from do_entry else do_from
  // TODO: implement
goto do_jump

do_jump:
from do_steps
if JUMP = 'EXIT goto do_exit else do_jump1

do_jump1:
from do_jump
  JUMP_TYPE ^= hd JUMP
  // TODO: implement more jump types
goto do_goto

do_exit:
from do_jump
  // nothing to do
goto stop

do_goto:
from do_jump1
  assert(JUMP_TYPE = 'GOTO)
  assert(LABEL_TO_FIND = 'nil)

  JUMP_TYPE ^= 'GOTO
  // save label of new block to find
  LABEL_TO_FIND ^= tl JUMP
goto restore_block

// put current block to the head of `BLOCKS`.
// then restore blocks from `SKCOLB` back to `BLOCKS`
restore_block:
from do_goto
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
exit
