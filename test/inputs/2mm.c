void func(double** tmp, double** A, double** B, double alpha)
{
  #pragma scop 
  for (int i = 0; i < 1024; i++)
    for (int j = 0; j < 1024; j++)
      {
        tmp[i][j] = 0.0;
        for (int k = 0; k < 1024; ++k)
          tmp[i][j] += alpha * A[i][k] * B[k][j];
      }
  #pragma endscop
}
