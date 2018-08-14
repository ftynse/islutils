/*
Test name: TEST(TreeMatcher, finderTest)

Given two matchers:
1. read(A,B)
2. read(D,B)

we expect:

C[i][j] and B[k][j]

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
      for(int k=0; k<N; ++k)
        C[i][j] += B[k][j] * A[i][k];
    }
  #pragma endscop
}
