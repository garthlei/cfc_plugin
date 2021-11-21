/**
  * @return instruction string of ctrlsig_s
  * G = G ^ (@param d)
  * if G == (@param S) then D = (@param D)
  * else raise an exception
  * !This function is NOT threadsafe!
  */
const char *inst_ctrlsig_s(int d, int S, int D);

/**
  * @return instruction string of ctrlsig_m
  * G = G ^ (@param d) ^ D
  * if G == (@param S) then D = (@param D)
  * else raise an exception
  * !This function is NOT threadsafe!
  */
const char *inst_ctrlsig_m(int d, int S, int D);