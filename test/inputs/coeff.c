/*
Test name: TEST(TreeMatcher, finderTest)

Given two matchers:
1. write(A,B)
2. read(B,D)


to be matched.
*/


#define N 1024

int A[N][N];
int B[N][N];
int C[N][N];

int main(){
  #pragma scop
  for(int i=0; i<N; ++i)
    for(int j=0; j<N; ++j) {
      A[i+1][j+i] = C[2*j][i+1];
    }
  #pragma endscop
}
