(prog input) -> (DECL BLOCKS BLOCKSREV NAME FROM STEPS JUMP BLOCK_IDX I TMP_NAME TMP_FROM TMP_STEPS TMP_JUMP TO_FIND) with ()

init:
entry
  I <- '0
  BLOCK_IDX <- '0
  (DECL . BLOCKS) <- prog
goto find_entry

find_entry: 
fi BLOCKSREV = 'nil from init else find_entry1
  ((TMP_NAME . (TMP_FROM . (TMP_STEPS . TMP_JUMP))) . BLOCKS) <- BLOCKS
if TMP_FROM = 'ENTRY goto found_entry else find_entry1

find_entry1:
from find_entry
  BLOCKSREV <- ((TMP_NAME . (TMP_FROM . (TMP_STEPS . TMP_JUMP))) . BLOCKSREV)
  I += '1
goto find_entry

found_entry:
from find_entry
  NAME  <- TMP_NAME
  FROM  <- TMP_FROM
  STEPS <- TMP_STEPS
  JUMP  <- TMP_JUMP
  BLOCK_IDX += I
goto found_entry1

found_entry1:
fi I = BLOCK_IDX from found_entry else found_entry1
  ((TMP_NAME . (TMP_FROM . (TMP_STEPS . TMP_JUMP))) . BLOCKSREV) <- BLOCKSREV
  BLOCKS <- ((TMP_NAME . (TMP_FROM . (TMP_STEPS . TMP_JUMP))) . BLOCKS)
  I -= '1
if I = '0 goto do_jump else found_entry1

// TODO: handle jumps other than goto
do_jump:
from found_entry1
goto do_goto

// TODO: handle jump to same block
do_goto:
from do_jump
  ('GOTO . TO_FIND) <- JUMP
goto find_block_idx

// Find index of block with name TO_FIND
find_block_idx: 
fi BLOCKSREV = 'nil from do_goto else find_block_idx1
  ((TMP_NAME . (TMP_FROM . (TMP_STEPS . TMP_JUMP))) . BLOCKS) <- BLOCKS
if TMP_NAME = TO_FIND goto foo else find_block_idx1

find_block_idx1:
from find_block_idx
  BLOCKSREV <- ((TMP_NAME . (TMP_FROM . (TMP_STEPS . TMP_JUMP))) . BLOCKSREV)
  I += '1
goto find_block_idx

foo:
from find_block_idx
goto stop

stop:
from foo
exit
