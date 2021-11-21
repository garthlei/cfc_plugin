// CUSTOM0: CTRLSIG_S/M
// 31302928272625242322212019181716151413121110 9 8 7 6 5 4 3 2 1 0
// +- - - - - - - -+- - - - - - - -+- - - - - - - -+-+- - - - - - -+
// | imm8 (d)      |   imm8 (S)    |   imm8 (D)    |C|   CUSTOM0   |
// +- - - - - - -+- - - - -+- - - - -+- - -+- - - - -+- - - - - - -+
// |  funct7     |  rs2    |  rs1    | f3  |   rd    |   CUSTOM0   |
// +---------------------------------------------------------------+ 
// C: 0-S 1-M

#include <cstdio>


/**
  * General ctrlsig function
  */
const char *_inst_ctrlsig(int d, int S, int D, int m)
{
    static char buffer[100];
    int funct7 = (d >> 1) & 0x7f;
    int rd = (D & 0xf) << 1;
    rd |= m&1;
    int f3 = (D >> 4) & 7;
    int rs1 = (D >> 7) &1;
    rs1 |= (S & 0xf) << 1;
    int rs2 = (S >> 4) & 0xf;
    rs2 |= (d & 1) << 4;
    sprintf(buffer,
    ".insn r CUSTOM_0, %d, %d, x%d, x%d, x%d # d(%d), s(%d), D(%d), m(%d)",
    f3, funct7, rd, rs1, rs2, d, S, D, m);
    return buffer;
}

/**
  * @return instruction string of ctrlsig_s
  * G = G ^ (@param d)
  * if G == (@param S) then D = (@param D)
  * else raise an exception
  * !This function is NOT threadsafe!
  */
const char *inst_ctrlsig_s(int d, int S, int D)
{
    return _inst_ctrlsig(d, S, D, 0);
}

/**
  * @return instruction string of ctrlsig_m
  * G = G ^ (@param d) ^ D
  * if G == (@param S) then D = (@param D)
  * else raise an exception
  * !This function is NOT threadsafe!
  */
const char *inst_ctrlsig_m(int d, int S, int D)
{
    return _inst_ctrlsig(d, S, D, 1);
}
