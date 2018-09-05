
int tmp[1024][1023];
int A[1024][1022];
int B[1022][1023];
int alpha;

void kernel1mm()
{

#pragma scop
  /* D := alpha*A*B*C + beta*D */
  for (int i = 0; i < 1024; i++)
    for (int j = 0; j < 1023; j++)
      {
	tmp[i][j] = 0;
	for (int k = 0; k < 1022; ++k)
	  tmp[i][j] += /*alpha **/ A[i][k] * B[k][j];
      }
#pragma endscop

}
