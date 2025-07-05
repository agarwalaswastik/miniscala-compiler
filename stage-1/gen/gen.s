.text
.global putchar, getchar, entry_point

################# FUNCTIONS #####################
fib:
	pushq %rbp	# save stack frame for calling convention
	movq %rsp, %rbp
	movq %rdi, %rsi
	movq $1, %rdx
	cmp %rdx, %rsi
	setle %al
	movzbq %al, %rsi
	cmpq $0, %rsi
	jne if1_then
	movq %rdi, %rsi
	movq $1, %rdx
	subq %rdx, %rsi
	pushq %rdi
	movq %rsi, %rdi
	call fib
	popq %rdi
	movq %rax, %rsi
	movq %rdi, %rdx
	movq $2, %rcx
	subq %rcx, %rdx
	pushq %rdi
	pushq %rsi
	movq %rdx, %rdi
	call fib
	popq %rsi
	popq %rdi
	movq %rax, %rdx
	addq %rdx, %rsi
	jmp if1_end
if1_then:
	movq %rdi, %rsi
if1_end:
	movq %rsi, %rax
	movq %rbp, %rsp	# reset frame
	popq %rbp
	ret

#################################################


###################### MAIN #####################
entry_point:
	pushq %rbp	# save stack frame for calling convention
	movq %rsp, %rbp
	movq %rdi, heap(%rip)
	pushq %rbx
	pushq %r12
	pushq %r13
	pushq %r14
	pushq %r15
	movq $5, %rdi
	imulq $8, %rdi
	movq heap(%rip), %rax
	addq %rdi, heap(%rip)
	movq %rax, %rdi
	movq $0, %rsi
	jmp loop2_cond
loop2_body:
	movq %rdi, %rdx
	movq %rsi, %rcx
	movq %rsi, %r8
	movq $5, %r9
	addq %r9, %r8
	pushq %rdi
	pushq %rsi
	pushq %rdx
	pushq %rcx
	movq %r8, %rdi
	call fib
	popq %rcx
	popq %rdx
	popq %rsi
	popq %rdi
	movq %rax, %r8
	movq %rcx, %rax
	imulq $8, %rax
	addq %rdx, %rax
	movq %r8, (%rax)
	movq %rsi, %rcx
	movq $1, %r8
	addq %r8, %rcx
	movq %rcx, %rsi
	movq $0, %r8
	movq %r8, %rcx
	movq %rcx, %rdx
loop2_cond:
	movq %rsi, %rdx
	movq $5, %rcx
	cmp %rcx, %rdx
	setl %al
	movzbq %al, %rdx
	cmpq $0, %rdx
	jne loop2_body
	movq %rdi, %rdx
	movq $4, %rcx
	movq %rcx, %rax
	imulq $8, %rax
	addq %rdx, %rax
	movq (%rax), %rdx
	movq %rdx, %rsi
	movq %rsi, %rdi
	movq %rdi, %rax
	popq %r15
	popq %r14
	popq %r13
	popq %r12
	popq %rbx
	movq %rbp, %rsp	# reset frame
	popq %rbp
	ret
#################################################


#################### DATA #######################

.data
heap:	.quad 0
#################################################
