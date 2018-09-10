
#define n 1024

int A[n];
int B[n];

int main(void){
  #pragma scop
  for(int i=0; i<n; i+=2) {
    A[i] = B[i+1];
  }
  #pragma endscop
}

