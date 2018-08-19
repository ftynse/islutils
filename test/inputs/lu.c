void kernel_lu(int n, double** A)
{
#pragma scop
  for (int i = 0; i < 400; i++) {
    for (int j = 0; j < i; j++) {
       for (int k = 0; k < j; k++) {
          A[i][j] -= A[i][k] * A[k][j];
       }
        A[i][j] /= A[j][j];
    }
   for (int j = i; j < 400; j++) {
       for (int k = 0; k < i; k++) {
          A[i][j] -= A[i][k] * A[k][j];
       }
    }
  }
#pragma endscop
}
