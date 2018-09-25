int tmp[1024][1024];
int A[1024][1024];
int B[1024][1024];
int D[1024][1024];
int alpha;

void kernel1mm() {
#pragma scop
  for (int j = 0; j < 1024; j++)
    for (int i = 0; i < 1024; i++) {
      for (int k = 0; k < 1024; k++) 
        tmp[i][j] = alpha * A[i][k] * B[k][j] + tmp[i][j];
    }
#pragma endscop
}
