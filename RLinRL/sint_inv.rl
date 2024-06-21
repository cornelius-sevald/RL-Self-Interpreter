(prog output) -> (prog input) with (STORE BLOCK LABEL COMES STEPS JUMP BLOCKS STEP STEP_TYPE COMES_TYPE JUMP_TYPE UPDATE_TYPE EXPR EXPR_TYPE PREV_LABEL UPDATE_VAR LOOKUP VAR VAL OP LABEL_TO_FIND VAR_TO_FIND STACK TMP FLAG FLAG_EVAL RES EXPR_L EXPR_R RES_L RES_R SPETS SKCOLB EROTS)

stop2:
	entry
	STORE <- output
	BLOCKS <- prog
	goto stop1

stop1:
	fi SKCOLB
		from stop1
		else stop2
	(BLOCK . BLOCKS) <- BLOCKS
	SKCOLB <- (BLOCK . SKCOLB)
	if BLOCKS
		goto stop1
		else do_exit

do_exit:
	from stop1
	(BLOCK . SKCOLB) <- SKCOLB
	(LABEL . (COMES . (STEPS . JUMP))) <- BLOCK
	assert((JUMP = 'EXIT))
	goto do_jump

do_jump:
	fi (JUMP = 'EXIT)
		from do_exit
		else do_jump1
	goto done_steps

done_steps:
	fi SPETS
		from done_steps_loop
		else do_jump
	if STEPS
		goto done_steps_loop
		else do_steps

done_steps_loop:
	from done_steps
	(STEP . STEPS) <- STEPS
	SPETS <- (STEP . SPETS)
	goto done_steps

do_steps:
	fi STEPS
		from do_steps_loop
		else done_steps
	if SPETS
		goto done_step
		else done_come_from

done_step:
	from do_steps
	(STEP . SPETS) <- SPETS
	if (STEP = 'SKIP)
		goto do_steps_loop
		else done_step1

do_steps_loop:
	fi (STEP = 'SKIP)
		from done_step
		else do_step1
	STEPS <- (STEP . STEPS)
	goto do_steps

done_step1:
	from done_step
	STEP_TYPE ^= hd(STEP)
	if (STEP_TYPE = 'ASSERT)
		goto done_assert
		else done_update

done_assert:
	from done_step1
	assert((EXPR = 'nil))
	EXPR ^= tl(STEP)
	goto done_assert1

done_assert1:
	fi FLAG_EVAL
		from do_eval_assert
		else done_assert
	if FLAG_EVAL
		goto do_assert2
		else done_eval_assert

do_assert2:
	from done_assert1
	assert(RES)
	goto done_eval_assert

done_eval_assert:
	fi FLAG_EVAL
		from do_assert2
		else done_assert1
	FLAG_EVAL ^= 'true
	FLAG <- ('ASSERT . FLAG)
	assert((hd(FLAG) = 'ASSERT))
	goto done_eval

done_eval:
	fi (hd(FLAG) = 'ASSERT)
		from done_eval_assert
		else done_eval_junction4
	EXPR_TYPE ^= hd(EXPR)
	if (EXPR_TYPE = 'CONST)
		goto eval_const
		else done_eval1

eval_const:
	from done_eval
	RES ^= tl(EXPR)
	assert((EXPR_TYPE = 'CONST))
	goto do_eval_junction5

do_eval_junction5:
	fi (EXPR_TYPE = 'CONST)
		from eval_const
		else do_eval1
	EXPR_TYPE ^= hd(EXPR)
	assert((EXPR_TYPE = 'nil))
	if (hd(FLAG) = 'ASSERT)
		goto do_eval_assert
		else do_eval_junction4

do_eval_assert:
	from do_eval_junction5
	('ASSERT . FLAG) <- FLAG
	if FLAG_EVAL
		goto done_assert1
		else do_assert

do_assert:
	from do_eval_assert
	EXPR ^= tl(STEP)
	assert((EXPR = 'nil))
	goto do_step1

do_step1:
	fi (STEP_TYPE = 'ASSERT)
		from do_assert
		else do_step2
	STEP_TYPE ^= hd(STEP)
	goto do_steps_loop

do_eval_junction4:
	from do_eval_junction5
	if (hd(FLAG) = 'OPERAND_R)
		goto do_eval_operand_right
		else do_eval_junction3

do_eval_operand_right:
	from do_eval_junction4
	('OPERAND_R . FLAG) <- FLAG
	if FLAG_EVAL
		goto done_eval_binop3
		else do_eval_binop2

done_eval_binop3:
	fi FLAG_EVAL
		from do_eval_operand_right
		else done_eval_binop2
	if FLAG_EVAL
		goto done_eval_binop5
		else done_eval_operand_right

done_eval_binop5:
	from done_eval_binop3
	RES_R <- RES
	(RES_L . STACK) <- STACK
	(OP . STACK) <- STACK
	(TMP . STACK) <- STACK
	if (OP = 'CONS)
		goto eval_cons
		else done_eval_binop6

eval_cons:
	from done_eval_binop5
	TMP ^= (RES_L . RES_R)
	goto do_eval_binop4

do_eval_binop4:
	fi (OP = 'CONS)
		from eval_cons
		else do_eval_binop6
	STACK <- (TMP . STACK)
	STACK <- (OP . STACK)
	STACK <- (RES_L . STACK)
	RES <- RES_R
	goto done_eval_operand_right

done_eval_operand_right:
	fi FLAG_EVAL
		from do_eval_binop4
		else done_eval_binop3
	FLAG_EVAL ^= 'true
	FLAG <- ('OPERAND_R . FLAG)
	assert((hd(FLAG) = 'OPERAND_R))
	goto done_eval_junction4

done_eval_junction4:
	fi (hd(FLAG) = 'OPERAND_R)
		from done_eval_operand_right
		else done_eval_junction3
	goto done_eval

done_eval_binop6:
	from done_eval_binop5
	if (OP = 'AND)
		goto eval_and
		else done_eval_binop7

eval_and:
	from done_eval_binop6
	TMP ^= (RES_L && RES_R)
	goto do_eval_binop6

do_eval_binop6:
	fi (OP = 'AND)
		from eval_and
		else do_eval_binop7
	goto do_eval_binop4

done_eval_binop7:
	from done_eval_binop6
	if (OP = 'OR)
		goto eval_or
		else done_eval_binop8

eval_or:
	from done_eval_binop7
	TMP ^= (RES_L || RES_R)
	goto do_eval_binop7

do_eval_binop7:
	fi (OP = 'OR)
		from eval_or
		else do_eval_binop8
	goto do_eval_binop6

done_eval_binop8:
	from done_eval_binop7
	if (OP = 'LESS)
		goto eval_less
		else done_eval_binop9

eval_less:
	from done_eval_binop8
	TMP ^= (RES_L < RES_R)
	goto do_eval_binop8

do_eval_binop8:
	fi (OP = 'LESS)
		from eval_less
		else do_eval_binop9
	goto do_eval_binop7

done_eval_binop9:
	from done_eval_binop8
	if (OP = 'GREATER)
		goto eval_greater
		else done_eval_binop10

eval_greater:
	from done_eval_binop9
	TMP ^= (RES_L > RES_R)
	goto do_eval_binop9

do_eval_binop9:
	fi (OP = 'GREATER)
		from eval_greater
		else do_eval_binop10
	goto do_eval_binop8

done_eval_binop10:
	from done_eval_binop9
	if (OP = 'EQUAL)
		goto eval_equal
		else done_eval_binop11

eval_equal:
	from done_eval_binop10
	TMP ^= (RES_L = RES_R)
	goto do_eval_binop10

do_eval_binop10:
	fi (OP = 'EQUAL)
		from eval_equal
		else do_eval_binop11
	goto do_eval_binop9

done_eval_binop11:
	from done_eval_binop10
	if (OP = 'ADD)
		goto eval_add
		else done_eval_binop12

eval_add:
	from done_eval_binop11
	TMP ^= (RES_L + RES_R)
	goto do_eval_binop11

do_eval_binop11:
	fi (OP = 'ADD)
		from eval_add
		else do_eval_binop12
	goto do_eval_binop10

done_eval_binop12:
	from done_eval_binop11
	if (OP = 'SUB)
		goto eval_sub
		else done_eval_binop13

eval_sub:
	from done_eval_binop12
	TMP ^= (RES_L - RES_R)
	goto do_eval_binop12

do_eval_binop12:
	fi (OP = 'SUB)
		from eval_sub
		else do_eval_binop13
	goto do_eval_binop11

done_eval_binop13:
	from done_eval_binop12
	if (OP = 'MUL)
		goto eval_mul
		else done_eval_binop14

eval_mul:
	from done_eval_binop13
	TMP ^= (RES_L * RES_R)
	goto do_eval_binop13

do_eval_binop13:
	fi (OP = 'MUL)
		from eval_mul
		else do_eval_binop14
	goto do_eval_binop12

done_eval_binop14:
	from done_eval_binop13
	if (OP = 'DIV)
		goto eval_div
		else do_eval_binop15

eval_div:
	from done_eval_binop14
	TMP ^= (RES_L / RES_R)
	goto do_eval_binop14

do_eval_binop14:
	fi (OP = 'DIV)
		from eval_div
		else do_eval_binop15
	goto do_eval_binop13

do_eval_binop15:
	from done_eval_binop14
	assert((OP = 'XOR))
	TMP ^= (RES_L ^ RES_R)
	assert((OP = 'XOR))
	goto do_eval_binop14

do_eval_binop2:
	from do_eval_operand_right
	(RES_L . STACK) <- STACK
	RES <- RES_L
	(OP . STACK) <- STACK
	(TMP . STACK) <- STACK
	((EXPR_L . EXPR_R) . STACK) <- STACK
	EXPR ^= EXPR_R
	EXPR ^= EXPR_L
	STACK <- ((EXPR_L . EXPR_R) . STACK)
	STACK <- (TMP . STACK)
	STACK <- (OP . STACK)
	FLAG_EVAL ^= 'true
	goto done_eval_operand_left

done_eval_operand_left:
	fi FLAG_EVAL
		from do_eval_binop2
		else done_eval_binop1
	FLAG_EVAL ^= 'true
	FLAG <- ('OPERAND_L . FLAG)
	assert((hd(FLAG) = 'OPERAND_L))
	goto done_eval_junction3

done_eval_junction3:
	fi (hd(FLAG) = 'OPERAND_L)
		from done_eval_operand_left
		else done_eval_junction2
	goto done_eval_junction4

do_eval_junction3:
	from do_eval_junction4
	if (hd(FLAG) = 'OPERAND_L)
		goto do_eval_operand_left
		else do_eval_junction2

do_eval_operand_left:
	from do_eval_junction3
	('OPERAND_L . FLAG) <- FLAG
	if FLAG_EVAL
		goto done_eval_binop1
		else do_eval3

done_eval_binop1:
	fi FLAG_EVAL
		from do_eval_operand_left
		else done_eval_binop
	if FLAG_EVAL
		goto done_eval_binop2
		else done_eval_operand_left

done_eval_binop2:
	from done_eval_binop1
	RES_L <- RES
	(OP . STACK) <- STACK
	(TMP . STACK) <- STACK
	((EXPR_L . EXPR_R) . STACK) <- STACK
	EXPR ^= EXPR_L
	EXPR ^= EXPR_R
	STACK <- ((EXPR_L . EXPR_R) . STACK)
	STACK <- (TMP . STACK)
	STACK <- (OP . STACK)
	STACK <- (RES_L . STACK)
	FLAG_EVAL ^= 'true
	goto done_eval_binop3

do_eval3:
	from do_eval_operand_left
	(OP . STACK) <- STACK
	(RES . STACK) <- STACK
	((EXPR_L . EXPR_R) . STACK) <- STACK
	EXPR ^= EXPR_L
	(FLAG_EVAL . STACK) <- STACK
	EXPR_TYPE ^= 'BINOP
	EXPR <- (EXPR_TYPE . (OP . (EXPR_L . EXPR_R)))
	EXPR_TYPE ^= 'BINOP
	assert((EXPR_TYPE = 'BINOP))
	goto do_eval2

do_eval2:
	fi (EXPR_TYPE = 'UNOP)
		from do_eval_unop
		else do_eval3
	goto do_eval1

do_eval1:
	fi (EXPR_TYPE = 'VAR)
		from eval_var
		else do_eval2
	goto do_eval_junction5

do_eval_junction2:
	from do_eval_junction3
	if (hd(FLAG) = 'OPERAND)
		goto do_eval_operand
		else do_eval_junction1

do_eval_operand:
	from do_eval_junction2
	('OPERAND . FLAG) <- FLAG
	if FLAG_EVAL
		goto done_eval_unop1
		else do_eval_unop

done_eval_unop1:
	fi FLAG_EVAL
		from do_eval_operand
		else done_eval_unop
	if FLAG_EVAL
		goto done_eval_unop2
		else done_eval_operand

done_eval_unop2:
	from done_eval_unop1
	(OP . STACK) <- STACK
	(TMP . STACK) <- STACK
	if (OP = 'NOT)
		goto eval_not
		else done_eval_unop3

eval_not:
	from done_eval_unop2
	TMP ^= !(RES)
	goto do_eval_unop2

do_eval_unop2:
	fi (OP = 'NOT)
		from eval_not
		else do_eval_unop3
	STACK <- (TMP . STACK)
	STACK <- (OP . STACK)
	goto done_eval_operand

done_eval_operand:
	fi FLAG_EVAL
		from do_eval_unop2
		else done_eval_unop1
	FLAG_EVAL ^= 'true
	FLAG <- ('OPERAND . FLAG)
	assert((hd(FLAG) = 'OPERAND))
	goto done_eval_junction2

done_eval_junction2:
	fi (hd(FLAG) = 'OPERAND)
		from done_eval_operand
		else done_eval_junction1
	goto done_eval_junction3

done_eval_unop3:
	from done_eval_unop2
	if (OP = 'HD)
		goto eval_hd
		else do_eval_unop4

eval_hd:
	from done_eval_unop3
	TMP ^= hd(RES)
	goto do_eval_unop3

do_eval_unop3:
	fi (OP = 'HD)
		from eval_hd
		else do_eval_unop4
	goto do_eval_unop2

do_eval_unop4:
	from done_eval_unop3
	assert((OP = 'TL))
	TMP ^= tl(RES)
	assert((OP = 'TL))
	goto do_eval_unop3

do_eval_unop:
	from do_eval_operand
	(OP . STACK) <- STACK
	(RES . STACK) <- STACK
	(FLAG_EVAL . STACK) <- STACK
	EXPR_TYPE ^= 'UNOP
	EXPR <- (EXPR_TYPE . (OP . EXPR))
	EXPR_TYPE ^= 'UNOP
	goto do_eval2

do_eval_junction1:
	from do_eval_junction2
	if (hd(FLAG) = 'UPDATE)
		goto do_eval_update
		else do_eval_junction

do_eval_update:
	from do_eval_junction1
	('UPDATE . FLAG) <- FLAG
	if FLAG_EVAL
		goto done_update1
		else do_step2

done_update1:
	fi FLAG_EVAL
		from do_eval_update
		else done_update
	if FLAG_EVAL
		goto undone_lookup_update
		else done_eval_update

undone_lookup_update:
	from done_update1
	assert((VAR_TO_FIND = 'nil))
	VAR_TO_FIND ^= UPDATE_VAR
	FLAG <- ('UPDATE . FLAG)
	goto undone_lookup

undone_lookup:
	fi (hd(FLAG) = 'EVAL)
		from undone_lookup_eval
		else undone_lookup_update
	goto undo_lookup1

undo_lookup1:
	fi EROTS
		from undo_lookup2
		else undone_lookup
	(LOOKUP . STORE) <- STORE
	if (hd(LOOKUP) = VAR_TO_FIND)
		goto undo_lookup
		else undo_lookup2

undo_lookup:
	from undo_lookup1
	if (hd(FLAG) = 'EVAL)
		goto done_lookup_eval
		else done_update3

done_lookup_eval:
	from undo_lookup
	('EVAL . FLAG) <- FLAG
	VAR_TO_FIND ^= tl(EXPR)
	assert((VAR_TO_FIND = 'nil))
	RES ^= tl(LOOKUP)
	assert((VAR_TO_FIND = 'nil))
	VAR_TO_FIND ^= tl(EXPR)
	FLAG <- ('EVAL . FLAG)
	goto done_lookup

done_lookup:
	fi (hd(FLAG) = 'EVAL)
		from done_lookup_eval
		else done_lookup_update
	goto do_lookup1

do_lookup1:
	fi (hd(LOOKUP) = VAR_TO_FIND)
		from done_lookup
		else do_lookup2
	STORE <- (LOOKUP . STORE)
	if EROTS
		goto do_lookup2
		else do_lookup

do_lookup2:
	from do_lookup1
	(LOOKUP . EROTS) <- EROTS
	goto do_lookup1

do_lookup:
	from do_lookup1
	if (hd(FLAG) = 'EVAL)
		goto eval_var
		else do_update2

eval_var:
	from do_lookup
	('EVAL . FLAG) <- FLAG
	VAR_TO_FIND ^= tl(EXPR)
	assert((VAR_TO_FIND = 'nil))
	assert((EXPR_TYPE = 'VAR))
	goto do_eval1

do_update2:
	from do_lookup
	('UPDATE . FLAG) <- FLAG
	VAR_TO_FIND ^= hd(tl(tl(STEP)))
	assert((VAR_TO_FIND = 'nil))
	goto done_eval_update

done_eval_update:
	fi FLAG_EVAL
		from do_update2
		else done_update1
	FLAG_EVAL ^= 'true
	FLAG <- ('UPDATE . FLAG)
	assert((hd(FLAG) = 'UPDATE))
	goto done_eval_junction1

done_eval_junction1:
	fi (hd(FLAG) = 'UPDATE)
		from done_eval_update
		else done_eval_junction
	goto done_eval_junction2

done_update3:
	from undo_lookup
	('UPDATE . FLAG) <- FLAG
	VAR_TO_FIND ^= UPDATE_VAR
	assert((VAR_TO_FIND = 'nil))
	(VAR . VAL) <- LOOKUP
	if (UPDATE_TYPE = 'ADD)
		goto do_update_add
		else done_update4

do_update_add:
	from done_update3
	VAL -= RES
	goto done_lookup_update

done_lookup_update:
	fi (UPDATE_TYPE = 'ADD)
		from do_update_add
		else do_update4
	LOOKUP <- (VAR . VAL)
	assert((VAR_TO_FIND = 'nil))
	VAR_TO_FIND ^= hd(tl(tl(STEP)))
	FLAG <- ('UPDATE . FLAG)
	goto done_lookup

done_update4:
	from done_update3
	if (UPDATE_TYPE = 'SUB)
		goto do_update_sub
		else do_update5

do_update_sub:
	from done_update4
	VAL += RES
	goto do_update4

do_update4:
	fi (UPDATE_TYPE = 'SUB)
		from do_update_sub
		else do_update5
	goto done_lookup_update

do_update5:
	from done_update4
	VAL ^= RES
	assert((UPDATE_TYPE = 'XOR))
	goto do_update4

undo_lookup2:
	from undo_lookup1
	EROTS <- (LOOKUP . EROTS)
	goto undo_lookup1

do_step2:
	from do_eval_update
	EXPR ^= tl(tl(tl(STEP)))
	UPDATE_VAR ^= hd(tl(tl(STEP)))
	UPDATE_TYPE ^= hd(tl(STEP))
	assert((UPDATE_TYPE = 'nil))
	assert((UPDATE_VAR = 'nil))
	assert((EXPR = 'nil))
	assert((STEP_TYPE = 'UPDATE))
	assert(!((STEP_TYPE = 'REPLACE)))
	goto do_step1

do_eval_junction:
	from do_eval_junction1
	if (hd(FLAG) = 'IF)
		goto do_eval_if
		else do_eval_fi

do_eval_if:
	from do_eval_junction
	('IF . FLAG) <- FLAG
	if FLAG_EVAL
		goto do_if4
		else do_if

do_if4:
	fi FLAG_EVAL
		from do_eval_if
		else done_if
	if FLAG_EVAL
		goto do_if3
		else done_eval_if

do_if3:
	from do_if4
	if RES
		goto do_if_true
		else do_if_false

do_if_true:
	from do_if3
	LABEL_TO_FIND ^= hd(tl(tl(JUMP)))
	goto do_if2

do_if2:
	fi RES
		from do_if_true
		else do_if_false
	goto done_eval_if

done_eval_if:
	fi FLAG_EVAL
		from do_if2
		else do_if4
	FLAG_EVAL ^= 'true
	FLAG <- ('IF . FLAG)
	assert((hd(FLAG) = 'IF))
	goto done_eval_junction

done_eval_junction:
	fi (hd(FLAG) = 'IF)
		from done_eval_if
		else done_eval_fi
	goto done_eval_junction1

do_if_false:
	from do_if3
	LABEL_TO_FIND ^= tl(tl(tl(JUMP)))
	goto do_if2

do_if:
	from do_eval_if
	EXPR ^= hd(tl(JUMP))
	assert((EXPR = 'nil))
	assert((JUMP_TYPE = 'IF))
	goto do_jump1

do_jump1:
	fi (JUMP_TYPE = 'GOTO)
		from do_goto
		else do_if
	JUMP_TYPE ^= hd(JUMP)
	goto do_jump

do_eval_fi:
	from do_eval_junction
	('FI . FLAG) <- FLAG
	if FLAG_EVAL
		goto do_fi4
		else do_fi

do_fi4:
	fi FLAG_EVAL
		from do_eval_fi
		else done_fi
	if FLAG_EVAL
		goto do_fi3
		else done_eval_fi

do_fi3:
	from do_fi4
	if RES
		goto do_fi_true
		else do_fi_false

do_fi_true:
	from do_fi3
	PREV_LABEL ^= hd(tl(tl(COMES)))
	goto do_fi2

do_fi2:
	fi RES
		from do_fi_true
		else do_fi_false
	goto done_eval_fi

done_eval_fi:
	fi FLAG_EVAL
		from do_fi2
		else do_fi4
	FLAG_EVAL ^= 'true
	FLAG <- ('FI . FLAG)
	assert((hd(FLAG) = 'FI))
	goto done_eval_junction

do_fi_false:
	from do_fi3
	PREV_LABEL ^= tl(tl(tl(COMES)))
	goto do_fi2

do_fi:
	from do_eval_fi
	EXPR ^= hd(tl(COMES))
	assert((EXPR = 'nil))
	assert((COMES_TYPE = 'FI))
	goto do_come_from1

do_come_from1:
	fi (COMES_TYPE = 'FROM)
		from do_from
		else do_fi
	COMES_TYPE ^= hd(COMES)
	goto main_loop

main_loop:
	fi (COMES = 'ENTRY)
		from done_come_from
		else do_come_from1
	if (COMES = 'ENTRY)
		goto init
		else find_block2

init:
	from main_loop
	input <- STORE
	BLOCK <- (LABEL . (COMES . (STEPS . JUMP)))
	prog <- (BLOCK . BLOCKS)
	exit

find_block2:
	from main_loop
	LABEL_TO_FIND ^= LABEL
	BLOCK <- (LABEL . (COMES . (STEPS . JUMP)))
	goto find_block

find_block:
	fi (hd(BLOCK) = LABEL_TO_FIND)
		from find_block2
		else find_block1
	BLOCKS <- (BLOCK . BLOCKS)
	if SKCOLB
		goto find_block1
		else restore_block1

find_block1:
	from find_block
	(BLOCK . SKCOLB) <- SKCOLB
	goto find_block

restore_block1:
	fi SKCOLB
		from restore_block2
		else find_block
	(BLOCK . BLOCKS) <- BLOCKS
	if (hd(BLOCK) = PREV_LABEL)
		goto done_jump
		else restore_block2

done_jump:
	from restore_block1
	(LABEL . (COMES . (STEPS . JUMP))) <- BLOCK
	PREV_LABEL ^= LABEL
	JUMP_TYPE ^= hd(JUMP)
	if (JUMP_TYPE = 'GOTO)
		goto do_goto
		else done_if

do_goto:
	from done_jump
	LABEL_TO_FIND ^= tl(JUMP)
	assert((LABEL_TO_FIND = 'nil))
	assert((JUMP_TYPE = 'GOTO))
	goto do_jump1

done_if:
	from done_jump
	assert((EXPR = 'nil))
	EXPR ^= hd(tl(JUMP))
	goto do_if4

restore_block2:
	from restore_block1
	SKCOLB <- (BLOCK . SKCOLB)
	goto restore_block1

done_eval1:
	from done_eval
	if (EXPR_TYPE = 'VAR)
		goto undone_lookup_eval
		else done_eval2

undone_lookup_eval:
	from done_eval1
	assert((VAR_TO_FIND = 'nil))
	VAR_TO_FIND ^= tl(EXPR)
	FLAG <- ('EVAL . FLAG)
	goto undone_lookup

done_eval2:
	from done_eval1
	if (EXPR_TYPE = 'UNOP)
		goto done_eval_unop
		else done_eval_binop

done_eval_unop:
	from done_eval2
	STACK <- (FLAG_EVAL . STACK)
	STACK <- (RES . STACK)
	EXPR_TYPE ^= 'UNOP
	(EXPR_TYPE . (OP . EXPR)) <- EXPR
	STACK <- (OP . STACK)
	EXPR_TYPE ^= 'UNOP
	goto done_eval_unop1

done_eval_binop:
	from done_eval2
	assert((EXPR_TYPE = 'BINOP))
	STACK <- (FLAG_EVAL . STACK)
	EXPR_TYPE ^= 'BINOP
	(EXPR_TYPE . (OP . (EXPR_L . EXPR_R))) <- EXPR
	EXPR ^= EXPR_L
	STACK <- ((EXPR_L . EXPR_R) . STACK)
	EXPR_TYPE ^= 'BINOP
	STACK <- (RES . STACK)
	STACK <- (OP . STACK)
	goto done_eval_binop1

done_update:
	from done_step1
	assert(!((STEP_TYPE = 'REPLACE)))
	assert((STEP_TYPE = 'UPDATE))
	assert((UPDATE_TYPE = 'nil))
	assert((UPDATE_VAR = 'nil))
	assert((EXPR = 'nil))
	EXPR ^= tl(tl(tl(STEP)))
	UPDATE_VAR ^= hd(tl(tl(STEP)))
	UPDATE_TYPE ^= hd(tl(STEP))
	goto done_update1

done_come_from:
	from do_steps
	if (COMES = 'ENTRY)
		goto main_loop
		else done_come_from1

done_come_from1:
	from done_come_from
	COMES_TYPE ^= hd(COMES)
	if (COMES_TYPE = 'FROM)
		goto do_from
		else done_fi

do_from:
	from done_come_from1
	PREV_LABEL ^= tl(COMES)
	assert((PREV_LABEL = tl(COMES)))
	assert((COMES_TYPE = 'FROM))
	goto do_come_from1

done_fi:
	from done_come_from1
	assert((EXPR = 'nil))
	EXPR ^= hd(tl(COMES))
	goto do_fi4
