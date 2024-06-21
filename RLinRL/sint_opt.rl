(prog input) -> (prog output) with (STORE BLOCK LABEL COMES STEPS JUMP BLOCKS STEP STEP_TYPE COMES_TYPE JUMP_TYPE UPDATE_TYPE EXPR EXPR_TYPE PREV_LABEL UPDATE_VAR LOOKUP VAR VAL OP LABEL_TO_FIND VAR_TO_FIND STACK TMP FLAG FLAG_EVAL RES EXPR_L EXPR_R RES_L RES_R SPETS SKCOLB EROTS)

stop2:
	from stop1
	prog <- BLOCKS
	output <- STORE
	exit

stop1:
	fi BLOCKS
		from stop1
		else do_exit
	(BLOCK . SKCOLB) <- SKCOLB
	BLOCKS <- (BLOCK . BLOCKS)
	if SKCOLB
		goto stop1
		else stop2

do_exit:
	from do_jump
	assert((JUMP = 'EXIT))
	BLOCK <- (LABEL . (COMES . (STEPS . JUMP)))
	SKCOLB <- (BLOCK . SKCOLB)
	goto stop1

do_jump:
	from done_steps
	if (JUMP = 'EXIT)
		goto do_exit
		else do_jump1

done_steps:
	fi STEPS
		from done_steps_loop
		else do_steps
	if SPETS
		goto done_steps_loop
		else do_jump

done_steps_loop:
	from done_steps
	(STEP . SPETS) <- SPETS
	STEPS <- (STEP . STEPS)
	goto done_steps

do_steps:
	fi SPETS
		from done_step
		else done_come_from
	if STEPS
		goto do_steps_loop
		else done_steps

done_step:
	fi (STEP = 'SKIP)
		from do_steps_loop
		else done_step1
	SPETS <- (STEP . SPETS)
	goto do_steps

do_steps_loop:
	from do_steps
	(STEP . STEPS) <- STEPS
	if (STEP = 'SKIP)
		goto done_step
		else do_step1

done_step1:
	fi (STEP_TYPE = 'ASSERT)
		from done_assert
		else done_update
	STEP_TYPE ^= hd(STEP)
	goto done_step

done_assert:
	from done_assert1
	EXPR ^= tl(STEP)
	assert((EXPR = 'nil))
	goto done_step1

done_assert1:
	fi FLAG_EVAL
		from do_assert2
		else done_eval_assert
	if FLAG_EVAL
		goto do_eval_assert
		else done_assert

do_assert2:
	from done_eval_assert
	assert(RES)
	goto done_assert1

done_eval_assert:
	from done_eval
	assert((hd(FLAG) = 'ASSERT))
	('ASSERT . FLAG) <- FLAG
	FLAG_EVAL ^= 'true
	if FLAG_EVAL
		goto do_assert2
		else done_assert1

done_eval:
	fi (EXPR_TYPE = 'CONST)
		from eval_const
		else done_eval1
	EXPR_TYPE ^= hd(EXPR)
	if (hd(FLAG) = 'ASSERT)
		goto done_eval_assert
		else done_eval_junction4

eval_const:
	from do_eval_junction5
	assert((EXPR_TYPE = 'CONST))
	RES ^= tl(EXPR)
	goto done_eval

do_eval_junction5:
	fi (hd(FLAG) = 'ASSERT)
		from do_eval_assert
		else do_eval_junction4
	assert((EXPR_TYPE = 'nil))
	EXPR_TYPE ^= hd(EXPR)
	if (EXPR_TYPE = 'CONST)
		goto eval_const
		else do_eval1

do_eval_assert:
	fi FLAG_EVAL
		from done_assert1
		else do_assert
	FLAG <- ('ASSERT . FLAG)
	goto do_eval_junction5

do_assert:
	from do_step1
	assert((EXPR = 'nil))
	EXPR ^= tl(STEP)
	goto do_eval_assert

do_step1:
	from do_steps_loop
	STEP_TYPE ^= hd(STEP)
	if (STEP_TYPE = 'ASSERT)
		goto do_assert
		else do_step2

do_eval_junction4:
	fi (hd(FLAG) = 'OPERAND_R)
		from do_eval_operand_right
		else do_eval_junction3
	goto do_eval_junction5

do_eval_operand_right:
	fi FLAG_EVAL
		from done_eval_binop3
		else do_eval_binop2
	FLAG <- ('OPERAND_R . FLAG)
	goto do_eval_junction4

done_eval_binop3:
	fi FLAG_EVAL
		from done_eval_binop5
		else done_eval_operand_right
	if FLAG_EVAL
		goto do_eval_operand_right
		else done_eval_binop2

done_eval_binop5:
	fi (OP = 'CONS)
		from eval_cons
		else done_eval_binop6
	STACK <- (TMP . STACK)
	STACK <- (OP . STACK)
	STACK <- (RES_L . STACK)
	RES <- RES_R
	goto done_eval_binop3

eval_cons:
	from do_eval_binop4
	TMP ^= (RES_L . RES_R)
	goto done_eval_binop5

do_eval_binop4:
	from done_eval_operand_right
	RES_R <- RES
	(RES_L . STACK) <- STACK
	(OP . STACK) <- STACK
	(TMP . STACK) <- STACK
	if (OP = 'CONS)
		goto eval_cons
		else do_eval_binop6

done_eval_operand_right:
	from done_eval_junction4
	assert((hd(FLAG) = 'OPERAND_R))
	('OPERAND_R . FLAG) <- FLAG
	FLAG_EVAL ^= 'true
	if FLAG_EVAL
		goto do_eval_binop4
		else done_eval_binop3

done_eval_junction4:
	from done_eval
	if (hd(FLAG) = 'OPERAND_R)
		goto done_eval_operand_right
		else done_eval_junction3

done_eval_binop6:
	fi (OP = 'AND)
		from eval_and
		else done_eval_binop7
	goto done_eval_binop5

eval_and:
	from do_eval_binop6
	TMP ^= (RES_L && RES_R)
	goto done_eval_binop6

do_eval_binop6:
	from do_eval_binop4
	if (OP = 'AND)
		goto eval_and
		else do_eval_binop7

done_eval_binop7:
	fi (OP = 'OR)
		from eval_or
		else done_eval_binop8
	goto done_eval_binop6

eval_or:
	from do_eval_binop7
	TMP ^= (RES_L || RES_R)
	goto done_eval_binop7

do_eval_binop7:
	from do_eval_binop6
	if (OP = 'OR)
		goto eval_or
		else do_eval_binop8

done_eval_binop8:
	fi (OP = 'LESS)
		from eval_less
		else done_eval_binop9
	goto done_eval_binop7

eval_less:
	from do_eval_binop8
	TMP ^= (RES_L < RES_R)
	goto done_eval_binop8

do_eval_binop8:
	from do_eval_binop7
	if (OP = 'LESS)
		goto eval_less
		else do_eval_binop9

done_eval_binop9:
	fi (OP = 'GREATER)
		from eval_greater
		else done_eval_binop10
	goto done_eval_binop8

eval_greater:
	from do_eval_binop9
	TMP ^= (RES_L > RES_R)
	goto done_eval_binop9

do_eval_binop9:
	from do_eval_binop8
	if (OP = 'GREATER)
		goto eval_greater
		else do_eval_binop10

done_eval_binop10:
	fi (OP = 'EQUAL)
		from eval_equal
		else done_eval_binop11
	goto done_eval_binop9

eval_equal:
	from do_eval_binop10
	TMP ^= (RES_L = RES_R)
	goto done_eval_binop10

do_eval_binop10:
	from do_eval_binop9
	if (OP = 'EQUAL)
		goto eval_equal
		else do_eval_binop11

done_eval_binop11:
	fi (OP = 'ADD)
		from eval_add
		else done_eval_binop12
	goto done_eval_binop10

eval_add:
	from do_eval_binop11
	TMP ^= (RES_L + RES_R)
	goto done_eval_binop11

do_eval_binop11:
	from do_eval_binop10
	if (OP = 'ADD)
		goto eval_add
		else do_eval_binop12

done_eval_binop12:
	fi (OP = 'SUB)
		from eval_sub
		else done_eval_binop13
	goto done_eval_binop11

eval_sub:
	from do_eval_binop12
	TMP ^= (RES_L - RES_R)
	goto done_eval_binop12

do_eval_binop12:
	from do_eval_binop11
	if (OP = 'SUB)
		goto eval_sub
		else do_eval_binop13

done_eval_binop13:
	fi (OP = 'MUL)
		from eval_mul
		else done_eval_binop14
	goto done_eval_binop12

eval_mul:
	from do_eval_binop13
	TMP ^= (RES_L * RES_R)
	goto done_eval_binop13

do_eval_binop13:
	from do_eval_binop12
	if (OP = 'MUL)
		goto eval_mul
		else do_eval_binop14

done_eval_binop14:
	fi (OP = 'DIV)
		from eval_div
		else do_eval_binop15
	goto done_eval_binop13

eval_div:
	from do_eval_binop14
	TMP ^= (RES_L / RES_R)
	goto done_eval_binop14

do_eval_binop14:
	from do_eval_binop13
	if (OP = 'DIV)
		goto eval_div
		else do_eval_binop15

do_eval_binop15:
	from do_eval_binop14
	assert((OP = 'XOR))
	TMP ^= (RES_L ^ RES_R)
	assert((OP = 'XOR))
	goto done_eval_binop14

do_eval_binop2:
	from done_eval_operand_left
	FLAG_EVAL ^= 'true
	(OP . STACK) <- STACK
	(TMP . STACK) <- STACK
	((EXPR_L . EXPR_R) . STACK) <- STACK
	EXPR ^= EXPR_L
	EXPR ^= EXPR_R
	STACK <- ((EXPR_L . EXPR_R) . STACK)
	STACK <- (TMP . STACK)
	STACK <- (OP . STACK)
	RES_L <- RES
	STACK <- (RES_L . STACK)
	goto do_eval_operand_right

done_eval_operand_left:
	from done_eval_junction3
	assert((hd(FLAG) = 'OPERAND_L))
	('OPERAND_L . FLAG) <- FLAG
	FLAG_EVAL ^= 'true
	if FLAG_EVAL
		goto do_eval_binop2
		else done_eval_binop1

done_eval_junction3:
	from done_eval_junction4
	if (hd(FLAG) = 'OPERAND_L)
		goto done_eval_operand_left
		else done_eval_junction2

do_eval_junction3:
	fi (hd(FLAG) = 'OPERAND_L)
		from do_eval_operand_left
		else do_eval_junction2
	goto do_eval_junction4

do_eval_operand_left:
	fi FLAG_EVAL
		from done_eval_binop1
		else do_eval3
	FLAG <- ('OPERAND_L . FLAG)
	goto do_eval_junction3

done_eval_binop1:
	fi FLAG_EVAL
		from done_eval_binop2
		else done_eval_operand_left
	if FLAG_EVAL
		goto do_eval_operand_left
		else done_eval_binop

done_eval_binop2:
	from done_eval_binop3
	FLAG_EVAL ^= 'true
	(RES_L . STACK) <- STACK
	(OP . STACK) <- STACK
	(TMP . STACK) <- STACK
	((EXPR_L . EXPR_R) . STACK) <- STACK
	EXPR ^= EXPR_R
	EXPR ^= EXPR_L
	STACK <- ((EXPR_L . EXPR_R) . STACK)
	STACK <- (TMP . STACK)
	STACK <- (OP . STACK)
	RES <- RES_L
	goto done_eval_binop1

do_eval3:
	from do_eval2
	assert((EXPR_TYPE = 'BINOP))
	EXPR_TYPE ^= 'BINOP
	(EXPR_TYPE . (OP . (EXPR_L . EXPR_R))) <- EXPR
	EXPR_TYPE ^= 'BINOP
	STACK <- (FLAG_EVAL . STACK)
	EXPR ^= EXPR_L
	STACK <- ((EXPR_L . EXPR_R) . STACK)
	STACK <- (RES . STACK)
	STACK <- (OP . STACK)
	goto do_eval_operand_left

do_eval2:
	from do_eval1
	if (EXPR_TYPE = 'UNOP)
		goto do_eval_unop
		else do_eval3

do_eval1:
	from do_eval_junction5
	if (EXPR_TYPE = 'VAR)
		goto eval_var
		else do_eval2

do_eval_junction2:
	fi (hd(FLAG) = 'OPERAND)
		from do_eval_operand
		else do_eval_junction1
	goto do_eval_junction3

do_eval_operand:
	fi FLAG_EVAL
		from done_eval_unop1
		else do_eval_unop
	FLAG <- ('OPERAND . FLAG)
	goto do_eval_junction2

done_eval_unop1:
	fi FLAG_EVAL
		from done_eval_unop2
		else done_eval_operand
	if FLAG_EVAL
		goto do_eval_operand
		else done_eval_unop

done_eval_unop2:
	fi (OP = 'NOT)
		from eval_not
		else done_eval_unop3
	STACK <- (TMP . STACK)
	STACK <- (OP . STACK)
	goto done_eval_unop1

eval_not:
	from do_eval_unop2
	TMP ^= !(RES)
	goto done_eval_unop2

do_eval_unop2:
	from done_eval_operand
	(OP . STACK) <- STACK
	(TMP . STACK) <- STACK
	if (OP = 'NOT)
		goto eval_not
		else do_eval_unop3

done_eval_operand:
	from done_eval_junction2
	assert((hd(FLAG) = 'OPERAND))
	('OPERAND . FLAG) <- FLAG
	FLAG_EVAL ^= 'true
	if FLAG_EVAL
		goto do_eval_unop2
		else done_eval_unop1

done_eval_junction2:
	from done_eval_junction3
	if (hd(FLAG) = 'OPERAND)
		goto done_eval_operand
		else done_eval_junction1

done_eval_unop3:
	fi (OP = 'HD)
		from eval_hd
		else do_eval_unop4
	goto done_eval_unop2

eval_hd:
	from do_eval_unop3
	TMP ^= hd(RES)
	goto done_eval_unop3

do_eval_unop3:
	from do_eval_unop2
	if (OP = 'HD)
		goto eval_hd
		else do_eval_unop4

do_eval_unop4:
	from do_eval_unop3
	assert((OP = 'TL))
	TMP ^= tl(RES)
	assert((OP = 'TL))
	goto done_eval_unop3

do_eval_unop:
	from do_eval2
	EXPR_TYPE ^= 'UNOP
	(EXPR_TYPE . (OP . EXPR)) <- EXPR
	EXPR_TYPE ^= 'UNOP
	STACK <- (FLAG_EVAL . STACK)
	STACK <- (RES . STACK)
	STACK <- (OP . STACK)
	goto do_eval_operand

do_eval_junction1:
	fi (hd(FLAG) = 'UPDATE)
		from do_eval_update
		else do_eval_junction
	goto do_eval_junction2

do_eval_update:
	fi FLAG_EVAL
		from done_update1
		else do_step2
	FLAG <- ('UPDATE . FLAG)
	goto do_eval_junction1

done_update1:
	fi FLAG_EVAL
		from undone_lookup_update
		else done_eval_update
	if FLAG_EVAL
		goto do_eval_update
		else done_update

undone_lookup_update:
	from undone_lookup
	('UPDATE . FLAG) <- FLAG
	VAR_TO_FIND ^= UPDATE_VAR
	assert((VAR_TO_FIND = 'nil))
	goto done_update1

undone_lookup:
	from undo_lookup1
	if (hd(FLAG) = 'EVAL)
		goto undone_lookup_eval
		else undone_lookup_update

undo_lookup1:
	fi (hd(LOOKUP) = VAR_TO_FIND)
		from undo_lookup
		else undo_lookup2
	STORE <- (LOOKUP . STORE)
	if EROTS
		goto undo_lookup2
		else undone_lookup

undo_lookup:
	fi (hd(FLAG) = 'EVAL)
		from done_lookup_eval
		else done_update3
	goto undo_lookup1

done_lookup_eval:
	from done_lookup
	('EVAL . FLAG) <- FLAG
	VAR_TO_FIND ^= tl(EXPR)
	assert((VAR_TO_FIND = 'nil))
	RES ^= tl(LOOKUP)
	assert((VAR_TO_FIND = 'nil))
	VAR_TO_FIND ^= tl(EXPR)
	FLAG <- ('EVAL . FLAG)
	goto undo_lookup

done_lookup:
	from do_lookup1
	if (hd(FLAG) = 'EVAL)
		goto done_lookup_eval
		else done_lookup_update

do_lookup1:
	fi EROTS
		from do_lookup2
		else do_lookup
	(LOOKUP . STORE) <- STORE
	if (hd(LOOKUP) = VAR_TO_FIND)
		goto done_lookup
		else do_lookup2

do_lookup2:
	from do_lookup1
	EROTS <- (LOOKUP . EROTS)
	goto do_lookup1

do_lookup:
	fi (hd(FLAG) = 'EVAL)
		from eval_var
		else do_update2
	goto do_lookup1

eval_var:
	from do_eval1
	assert((EXPR_TYPE = 'VAR))
	assert((VAR_TO_FIND = 'nil))
	VAR_TO_FIND ^= tl(EXPR)
	FLAG <- ('EVAL . FLAG)
	goto do_lookup

do_update2:
	from done_eval_update
	assert((VAR_TO_FIND = 'nil))
	VAR_TO_FIND ^= hd(tl(tl(STEP)))
	FLAG <- ('UPDATE . FLAG)
	goto do_lookup

done_eval_update:
	from done_eval_junction1
	assert((hd(FLAG) = 'UPDATE))
	('UPDATE . FLAG) <- FLAG
	FLAG_EVAL ^= 'true
	if FLAG_EVAL
		goto do_update2
		else done_update1

done_eval_junction1:
	from done_eval_junction2
	if (hd(FLAG) = 'UPDATE)
		goto done_eval_update
		else done_eval_junction

done_update3:
	fi (UPDATE_TYPE = 'ADD)
		from do_update_add
		else done_update4
	LOOKUP <- (VAR . VAL)
	assert((VAR_TO_FIND = 'nil))
	VAR_TO_FIND ^= UPDATE_VAR
	FLAG <- ('UPDATE . FLAG)
	goto undo_lookup

do_update_add:
	from done_lookup_update
	VAL += RES
	goto done_update3

done_lookup_update:
	from done_lookup
	('UPDATE . FLAG) <- FLAG
	VAR_TO_FIND ^= hd(tl(tl(STEP)))
	assert((VAR_TO_FIND = 'nil))
	(VAR . VAL) <- LOOKUP
	if (UPDATE_TYPE = 'ADD)
		goto do_update_add
		else do_update4

done_update4:
	fi (UPDATE_TYPE = 'SUB)
		from do_update_sub
		else do_update5
	goto done_update3

do_update_sub:
	from do_update4
	VAL -= RES
	goto done_update4

do_update4:
	from done_lookup_update
	if (UPDATE_TYPE = 'SUB)
		goto do_update_sub
		else do_update5

do_update5:
	from do_update4
	assert((UPDATE_TYPE = 'XOR))
	VAL ^= RES
	goto done_update4

undo_lookup2:
	from undo_lookup1
	(LOOKUP . EROTS) <- EROTS
	goto undo_lookup1

do_step2:
	from do_step1
	assert(!((STEP_TYPE = 'REPLACE)))
	assert((STEP_TYPE = 'UPDATE))
	assert((EXPR = 'nil))
	assert((UPDATE_VAR = 'nil))
	assert((UPDATE_TYPE = 'nil))
	UPDATE_TYPE ^= hd(tl(STEP))
	UPDATE_VAR ^= hd(tl(tl(STEP)))
	EXPR ^= tl(tl(tl(STEP)))
	goto do_eval_update

do_eval_junction:
	fi (hd(FLAG) = 'IF)
		from do_eval_if
		else do_eval_fi
	goto do_eval_junction1

do_eval_if:
	fi FLAG_EVAL
		from do_if4
		else do_if
	FLAG <- ('IF . FLAG)
	goto do_eval_junction

do_if4:
	fi FLAG_EVAL
		from do_if3
		else done_eval_if
	if FLAG_EVAL
		goto do_eval_if
		else done_if

do_if3:
	fi RES
		from do_if_true
		else do_if_false
	goto do_if4

do_if_true:
	from do_if2
	LABEL_TO_FIND ^= hd(tl(tl(JUMP)))
	goto do_if3

do_if2:
	from done_eval_if
	if RES
		goto do_if_true
		else do_if_false

done_eval_if:
	from done_eval_junction
	assert((hd(FLAG) = 'IF))
	('IF . FLAG) <- FLAG
	FLAG_EVAL ^= 'true
	if FLAG_EVAL
		goto do_if2
		else do_if4

done_eval_junction:
	from done_eval_junction1
	if (hd(FLAG) = 'IF)
		goto done_eval_if
		else done_eval_fi

do_if_false:
	from do_if2
	LABEL_TO_FIND ^= tl(tl(tl(JUMP)))
	goto do_if3

do_if:
	from do_jump1
	assert((JUMP_TYPE = 'IF))
	assert((EXPR = 'nil))
	EXPR ^= hd(tl(JUMP))
	goto do_eval_if

do_jump1:
	from do_jump
	JUMP_TYPE ^= hd(JUMP)
	if (JUMP_TYPE = 'GOTO)
		goto do_goto
		else do_if

do_eval_fi:
	fi FLAG_EVAL
		from do_fi4
		else do_fi
	FLAG <- ('FI . FLAG)
	goto do_eval_junction

do_fi4:
	fi FLAG_EVAL
		from do_fi3
		else done_eval_fi
	if FLAG_EVAL
		goto do_eval_fi
		else done_fi

do_fi3:
	fi RES
		from do_fi_true
		else do_fi_false
	goto do_fi4

do_fi_true:
	from do_fi2
	PREV_LABEL ^= hd(tl(tl(COMES)))
	goto do_fi3

do_fi2:
	from done_eval_fi
	if RES
		goto do_fi_true
		else do_fi_false

done_eval_fi:
	from done_eval_junction
	assert((hd(FLAG) = 'FI))
	('FI . FLAG) <- FLAG
	FLAG_EVAL ^= 'true
	if FLAG_EVAL
		goto do_fi2
		else do_fi4

do_fi_false:
	from do_fi2
	PREV_LABEL ^= tl(tl(tl(COMES)))
	goto do_fi3

do_fi:
	from do_come_from1
	assert((COMES_TYPE = 'FI))
	assert((EXPR = 'nil))
	EXPR ^= hd(tl(COMES))
	goto do_eval_fi

do_come_from1:
	from main_loop
	COMES_TYPE ^= hd(COMES)
	if (COMES_TYPE = 'FROM)
		goto do_from
		else do_fi

main_loop:
	fi (COMES = 'ENTRY)
		from init
		else find_block2
	if (COMES = 'ENTRY)
		goto done_come_from
		else do_come_from1

init:
	entry
	(BLOCK . BLOCKS) <- prog
	(LABEL . (COMES . (STEPS . JUMP))) <- BLOCK
	STORE <- input
	goto main_loop

find_block2:
	from find_block
	(LABEL . (COMES . (STEPS . JUMP))) <- BLOCK
	LABEL_TO_FIND ^= LABEL
	goto main_loop

find_block:
	fi SKCOLB
		from find_block1
		else restore_block1
	(BLOCK . BLOCKS) <- BLOCKS
	if (hd(BLOCK) = LABEL_TO_FIND)
		goto find_block2
		else find_block1

find_block1:
	from find_block
	SKCOLB <- (BLOCK . SKCOLB)
	goto find_block

restore_block1:
	fi (hd(BLOCK) = PREV_LABEL)
		from done_jump
		else restore_block2
	BLOCKS <- (BLOCK . BLOCKS)
	if SKCOLB
		goto restore_block2
		else find_block

done_jump:
	fi (JUMP_TYPE = 'GOTO)
		from do_goto
		else done_if
	JUMP_TYPE ^= hd(JUMP)
	PREV_LABEL ^= LABEL
	BLOCK <- (LABEL . (COMES . (STEPS . JUMP)))
	goto restore_block1

do_goto:
	from do_jump1
	assert((JUMP_TYPE = 'GOTO))
	assert((LABEL_TO_FIND = 'nil))
	LABEL_TO_FIND ^= tl(JUMP)
	goto done_jump

done_if:
	from do_if4
	EXPR ^= hd(tl(JUMP))
	assert((EXPR = 'nil))
	goto done_jump

restore_block2:
	from restore_block1
	(BLOCK . SKCOLB) <- SKCOLB
	goto restore_block1

done_eval1:
	fi (EXPR_TYPE = 'VAR)
		from undone_lookup_eval
		else done_eval2
	goto done_eval

undone_lookup_eval:
	from undone_lookup
	('EVAL . FLAG) <- FLAG
	VAR_TO_FIND ^= tl(EXPR)
	assert((VAR_TO_FIND = 'nil))
	goto done_eval1

done_eval2:
	fi (EXPR_TYPE = 'UNOP)
		from done_eval_unop
		else done_eval_binop
	goto done_eval1

done_eval_unop:
	from done_eval_unop1
	EXPR_TYPE ^= 'UNOP
	(OP . STACK) <- STACK
	EXPR <- (EXPR_TYPE . (OP . EXPR))
	EXPR_TYPE ^= 'UNOP
	(RES . STACK) <- STACK
	(FLAG_EVAL . STACK) <- STACK
	goto done_eval2

done_eval_binop:
	from done_eval_binop1
	(OP . STACK) <- STACK
	(RES . STACK) <- STACK
	EXPR_TYPE ^= 'BINOP
	((EXPR_L . EXPR_R) . STACK) <- STACK
	EXPR ^= EXPR_L
	EXPR <- (EXPR_TYPE . (OP . (EXPR_L . EXPR_R)))
	EXPR_TYPE ^= 'BINOP
	(FLAG_EVAL . STACK) <- STACK
	assert((EXPR_TYPE = 'BINOP))
	goto done_eval2

done_update:
	from done_update1
	UPDATE_TYPE ^= hd(tl(STEP))
	UPDATE_VAR ^= hd(tl(tl(STEP)))
	EXPR ^= tl(tl(tl(STEP)))
	assert((EXPR = 'nil))
	assert((UPDATE_VAR = 'nil))
	assert((UPDATE_TYPE = 'nil))
	assert((STEP_TYPE = 'UPDATE))
	assert(!((STEP_TYPE = 'REPLACE)))
	goto done_step1

done_come_from:
	fi (COMES = 'ENTRY)
		from main_loop
		else done_come_from1
	goto do_steps

done_come_from1:
	fi (COMES_TYPE = 'FROM)
		from do_from
		else done_fi
	COMES_TYPE ^= hd(COMES)
	goto done_come_from

do_from:
	from do_come_from1
	assert((COMES_TYPE = 'FROM))
	assert((PREV_LABEL = tl(COMES)))
	PREV_LABEL ^= tl(COMES)
	goto done_come_from1

done_fi:
	from do_fi4
	EXPR ^= hd(tl(COMES))
	assert((EXPR = 'nil))
	goto done_come_from1
