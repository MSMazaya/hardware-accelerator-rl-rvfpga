in=decode
out=decode.out
view=rv32i
.i 32
.o 1
.ilb  i[31] i[30] i[29] i[28] i[27] i[26] i[25] i[24] i[23] i[22] i[21] i[20] i[19] i[18] i[17] i[16] i[15] i[14] i[13] i[12] i[11] i[10] i[9] i[8] i[7] i[6] i[5] i[4] i[3] i[2] i[1] i[0]
.ob legal
.type fd
# add
0000000----------000-----0110011 1
# addi
-----------------000-----0010011 1
# and
0000000----------111-----0110011 1
# andi
-----------------111-----0010011 1
# andn
0100000----------111-----0110011 1
# auipc
-------------------------0010111 1
# bclr
0100100----------001-----0110011 1
# bclri
0100100----------001-----0010011 1
# bcompress
0000100----------110-----0110011 1
# bdecompress
0100100----------110-----0110011 1
# beq
-----------------000-----1100011 1
# bext
0100100----------101-----0110011 1
# bexti
0100100----------101-----0010011 1
# bfp
0100100----------111-----0110011 1
# bge
-----------------101-----1100011 1
# bgeu
-----------------111-----1100011 1
# binv
0110100----------001-----0110011 1
# binvi
0110100----------001-----0010011 1
# blt
-----------------100-----1100011 1
# bltu
-----------------110-----1100011 1
# bne
-----------------001-----1100011 1
# bset
0010100----------001-----0110011 1
# bseti
0010100----------001-----0010011 1
# clmul
0000101----------001-----0110011 1
# clmulh
0000101----------011-----0110011 1
# clmulr
0000101----------010-----0110011 1
# clz
011000000000-----001-----0010011 1
# cpop
011000000010-----001-----0010011 1
# crc32_b
011000010000-----001-----0010011 1
# crc32_h
011000010001-----001-----0010011 1
# crc32_w
011000010010-----001-----0010011 1
# crc32c_b
011000011000-----001-----0010011 1
# crc32c_h
011000011001-----001-----0010011 1
# crc32c_w
011000011010-----001-----0010011 1
# csrrc_ro
------------00000011-----1110011 1
# csrrc_rw0
------------1----011-----1110011 1
# csrrc_rw1
-------------1---011-----1110011 1
# csrrc_rw2
--------------1--011-----1110011 1
# csrrc_rw3
---------------1-011-----1110011 1
# csrrc_rw4
----------------1011-----1110011 1
# csrrci_ro
------------00000111-----1110011 1
# csrrci_rw0
------------1----111-----1110011 1
# csrrci_rw1
-------------1---111-----1110011 1
# csrrci_rw2
--------------1--111-----1110011 1
# csrrci_rw3
---------------1-111-----1110011 1
# csrrci_rw4
----------------1111-----1110011 1
# csrrs_ro
------------00000010-----1110011 1
# csrrs_rw0
------------1----010-----1110011 1
# csrrs_rw1
-------------1---010-----1110011 1
# csrrs_rw2
--------------1--010-----1110011 1
# csrrs_rw3
---------------1-010-----1110011 1
# csrrs_rw4
----------------1010-----1110011 1
# csrrsi_ro
------------00000110-----1110011 1
# csrrsi_rw0
------------1----110-----1110011 1
# csrrsi_rw1
-------------1---110-----1110011 1
# csrrsi_rw2
--------------1--110-----1110011 1
# csrrsi_rw3
---------------1-110-----1110011 1
# csrrsi_rw4
----------------1110-----1110011 1
# csrrw0
-----------------001----11110011 1
# csrrw1
-----------------001---1-1110011 1
# csrrw2
-----------------001--1--1110011 1
# csrrw3
-----------------001-1---1110011 1
# csrrw4
-----------------0011----1110011 1
# csrrwi0
-----------------101----11110011 1
# csrrwi1
-----------------101---1-1110011 1
# csrrwi2
-----------------101--1--1110011 1
# csrrwi3
-----------------101-1---1110011 1
# csrrwi4
-----------------1011----1110011 1
# csrw
-----------------001000001110011 1
# csrwi
-----------------101000001110011 1
# ctz
011000000001-----001-----0010011 1
# div
0000001----------100-----0110011 1
# divu
0000001----------101-----0110011 1
# ebreak
00000000000100000000000001110011 1
# ecall
00000000000000000000000001110011 1
# fadd
0000000------------------1010011 1
# fdiv
0001100------------------1010011 1
# fence
0000--------00000000000000001111 1
# fence.i
00000000000000000001000000001111 1
# fmul
0001000------------------1010011 1
# gorc
0010100----------101-----0110011 1
# gorci0
001010000000-----101-----0010011 1
# gorci1
001010000001-----101-----0010011 1
# gorci10
001010001010-----101-----0010011 1
# gorci11
001010001011-----101-----0010011 1
# gorci12
001010001100-----101-----0010011 1
# gorci13
001010001101-----101-----0010011 1
# gorci14
001010001110-----101-----0010011 1
# gorci15
001010001111-----101-----0010011 1
# gorci16
001010010000-----101-----0010011 1
# gorci17
001010010001-----101-----0010011 1
# gorci18
001010010010-----101-----0010011 1
# gorci19
001010010011-----101-----0010011 1
# gorci2
001010000010-----101-----0010011 1
# gorci20
001010010100-----101-----0010011 1
# gorci21
001010010101-----101-----0010011 1
# gorci22
001010010110-----101-----0010011 1
# gorci23
001010010111-----101-----0010011 1
# gorci24
001010011000-----101-----0010011 1
# gorci25
001010011001-----101-----0010011 1
# gorci26
001010011010-----101-----0010011 1
# gorci27
001010011011-----101-----0010011 1
# gorci28
001010011100-----101-----0010011 1
# gorci29
001010011101-----101-----0010011 1
# gorci3
001010000011-----101-----0010011 1
# gorci30
001010011110-----101-----0010011 1
# gorci31
001010011111-----101-----0010011 1
# gorci4
001010000100-----101-----0010011 1
# gorci5
001010000101-----101-----0010011 1
# gorci6
001010000110-----101-----0010011 1
# gorci8
001010001000-----101-----0010011 1
# gorci9
001010001001-----101-----0010011 1
# grev
0110100----------101-----0110011 1
# grevi0
011010000000-----101-----0010011 1
# grevi1
011010000001-----101-----0010011 1
# grevi10
011010001010-----101-----0010011 1
# grevi11
011010001011-----101-----0010011 1
# grevi12
011010001100-----101-----0010011 1
# grevi13
011010001101-----101-----0010011 1
# grevi14
011010001110-----101-----0010011 1
# grevi15
011010001111-----101-----0010011 1
# grevi16
011010010000-----101-----0010011 1
# grevi17
011010010001-----101-----0010011 1
# grevi18
011010010010-----101-----0010011 1
# grevi19
011010010011-----101-----0010011 1
# grevi2
011010000010-----101-----0010011 1
# grevi20
011010010100-----101-----0010011 1
# grevi21
011010010101-----101-----0010011 1
# grevi22
011010010110-----101-----0010011 1
# grevi23
011010010111-----101-----0010011 1
# grevi25
011010011001-----101-----0010011 1
# grevi26
011010011010-----101-----0010011 1
# grevi27
011010011011-----101-----0010011 1
# grevi28
011010011100-----101-----0010011 1
# grevi29
011010011101-----101-----0010011 1
# grevi3
011010000011-----101-----0010011 1
# grevi30
011010011110-----101-----0010011 1
# grevi31
011010011111-----101-----0010011 1
# grevi4
011010000100-----101-----0010011 1
# grevi5
011010000101-----101-----0010011 1
# grevi6
011010000110-----101-----0010011 1
# grevi7
011010000111-----101-----0010011 1
# grevi8
011010001000-----101-----0010011 1
# grevi9
011010001001-----101-----0010011 1
# jal
-------------------------1101111 1
# jalr
-----------------000-----1100111 1
# lb
-----------------000-----0000011 1
# lbu
-----------------100-----0000011 1
# lh
-----------------001-----0000011 1
# lhu
-----------------101-----0000011 1
# lui
-------------------------0110111 1
# lw
-----------------010-----0000011 1
# max
0000101----------110-----0110011 1
# maxu
0000101----------111-----0110011 1
# min
0000101----------100-----0110011 1
# minu
0000101----------101-----0110011 1
# mret
00110000001000000000000001110011 1
# mul
0000001----------000-----0110011 1
# mulh
0000001----------001-----0110011 1
# mulhsu
0000001----------010-----0110011 1
# mulhu
0000001----------011-----0110011 1
# or
0000000----------110-----0110011 1
# orc_b
001010000111-----101-----0010011 1
# ori
-----------------110-----0010011 1
# orn
0100000----------110-----0110011 1
# pack1
000010000001-----100-----0110011 1
# pack10
000010001010-----100-----0110011 1
# pack11
000010001011-----100-----0110011 1
# pack12
000010001100-----100-----0110011 1
# pack13
000010001101-----100-----0110011 1
# pack14
000010001110-----100-----0110011 1
# pack15
000010001111-----100-----0110011 1
# pack16
000010010000-----100-----0110011 1
# pack17
000010010001-----100-----0110011 1
# pack18
000010010010-----100-----0110011 1
# pack19
000010010011-----100-----0110011 1
# pack2
000010000010-----100-----0110011 1
# pack20
000010010100-----100-----0110011 1
# pack21
000010010101-----100-----0110011 1
# pack22
000010010110-----100-----0110011 1
# pack23
000010010111-----100-----0110011 1
# pack24
000010011000-----100-----0110011 1
# pack25
000010011001-----100-----0110011 1
# pack26
000010011010-----100-----0110011 1
# pack27
000010011011-----100-----0110011 1
# pack28
000010011100-----100-----0110011 1
# pack29
000010011101-----100-----0110011 1
# pack3
000010000011-----100-----0110011 1
# pack30
000010011110-----100-----0110011 1
# pack31
000010011111-----100-----0110011 1
# pack4
000010000100-----100-----0110011 1
# pack5
000010000101-----100-----0110011 1
# pack6
000010000110-----100-----0110011 1
# pack7
000010000111-----100-----0110011 1
# pack8
000010001000-----100-----0110011 1
# pack9
000010001001-----100-----0110011 1
# packh
0000100----------111-----0110011 1
# packu
0100100----------100-----0110011 1
# rem
0000001----------110-----0110011 1
# remu
0000001----------111-----0110011 1
# rev8
011010011000-----101-----0010011 1
# rol
0110000----------001-----0110011 1
# ror
0110000----------101-----0110011 1
# rori
0110000----------101-----0010011 1
# sb
-----------------000-----0100011 1
# sext_b
011000000100-----001-----0010011 1
# sext_h
011000000101-----001-----0010011 1
# sh
-----------------001-----0100011 1
# sh1add
0010000----------010-----0110011 1
# sh2add
0010000----------100-----0110011 1
# sh3add
0010000----------110-----0110011 1
# shfl
0000100----------001-----0110011 1
# shfli
00001000---------001-----0010011 1
# sll
0000000----------001-----0110011 1
# slli
0000000----------001-----0010011 1
# slt
0000000----------010-----0110011 1
# slti
-----------------010-----0010011 1
# sltiu
-----------------011-----0010011 1
# sltu
0000000----------011-----0110011 1
# sra
0100000----------101-----0110011 1
# srai
0100000----------101-----0010011 1
# srl
0000000----------101-----0110011 1
# srli
0000000----------101-----0010011 1
# sub
0100000----------000-----0110011 1
# sw
-----------------010-----0100011 1
# unshfl
0000100----------101-----0110011 1
# unshfli
00001000---------101-----0010011 1
# wfi
00010000010100000000000001110011 1
# xnor
0100000----------100-----0110011 1
# xor
0000000----------100-----0110011 1
# xori
-----------------100-----0010011 1
# xperm_b
0010100----------100-----0110011 1
# xperm_h
0010100----------110-----0110011 1
# xperm_n
0010100----------010-----0110011 1
# zext_h
000010000000-----100-----0110011 1
