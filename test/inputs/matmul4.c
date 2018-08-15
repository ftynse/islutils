/*
Test name: TEST(TreeMatcher, finderTest)

Given two matchers:
1. read(A,B)
2. read(A,D)

we expect:

C[2i][j+1] and A[2i][k]

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
        C[2*i][j+1] += B[k][j+1] * A[2*i][k];
    }
  #pragma endscop
}
