#include <islutils/builders.h>
#include <islutils/matchers.h>
#include <islutils/parser.h>
#include <iostream>

#include "gtest/gtest.h"

//##############################
// helper function for debug.
void printMatches(std::vector<matchers::memoryAccess> &m) {
  std::cout << "####" << std::endl;
  for(size_t i=0; i<m.size(); ++i) {
    std::cout << m[i] << std::endl;
  }
}

// count read 
int countReadMatched(std::vector<matchers::memoryAccess> &m) {
  int res = 0;
  for(size_t i=0; i<m.size(); ++i) {
    if((m[i].type_ == matchers::RelationKind::read) ||
       (m[i].type_ == matchers::RelationKind::readAndWrite))
      res++;
  }
  return res;
}

// count write
int countWriteMatched(std::vector<matchers::memoryAccess> &m) {
  int res = 0;
  for(size_t i=0; i<m.size(); ++i) {
    if((m[i].type_ == matchers::RelationKind::write) ||
       (m[i].type_ == matchers::RelationKind::readAndWrite))
      res++;
  }
  return res;
}

// check the Scop
Scop checkScop(std::string s) {
  Scop S = Parser(s).getScop();
  EXPECT_TRUE(!S.schedule.is_null());
  return S;
}

// check not empty read and write
void checkReadAndWrite(Scop S) {
  isl::union_map reads = S.reads;
  isl::union_map writes = S.mustWrites;
  EXPECT_TRUE(reads.n_map() != 0);
  EXPECT_TRUE(writes.n_map() != 0);
}
//##############################


/*
TEST(AccessMatcher, ReadFromFile) {
  Scop S = Parser("inputs/one-dimensional-init.c").getScop();
  EXPECT_TRUE(!S.schedule.is_null());
}

TEST(AccessMatcher, CompileTest) {
  using namespace matchers;

  // access pattern matchers.
  auto ctx = isl::ctx(isl_ctx_alloc());
  isl::val v = isl::val(ctx,1);
  PlaceHolder dummy = PlaceHolder(v,v,v,1);
  auto m12 = read('X', dummy);
  auto m13 = read('X', dummy, 'Y', dummy);
  auto m14 = write('Z', dummy);
  auto m15 = write('S', dummy, 'Y', dummy);
  auto m16 = readAndWrite('X', dummy, 'Y', dummy);
  isl_ctx_free(ctx.release());
}

TEST(AccessMatcher, matmul1) {
  using namespace matchers;
  auto ctx = isl::ctx(isl_ctx_alloc());

  isl::val Zero = isl::val(ctx,0);
  isl::val One = isl::val(ctx,1);
  PlaceHolder dummy = PlaceHolder(One,Zero,Zero,1);
  auto m1 = read('A', dummy, 'B', dummy);
  auto m2 = read('D', dummy, 'B', dummy);
  Scop S = checkScop("inputs/matmul1.c");
  checkReadAndWrite(S);
  std::vector<RelationMatcher> v;
  v.push_back(m1);
  v.push_back(m2);
  Finder f = Finder(S.reads, S.mustWrites, v);
  std::vector<memoryAccess> res;
  res = f.find();
  //printMatches(res);
  EXPECT_TRUE(res.size() == 2);
  int counter = countReadMatched(res);
  EXPECT_TRUE(counter == 2);
  counter = countWriteMatched(res);
  EXPECT_TRUE(counter == 0);
  isl_ctx_free(ctx.release());
}

TEST(AccessMatcher, matmul2) {
  using namespace matchers;
  auto ctx = isl::ctx(isl_ctx_alloc());

  isl::val Zero = isl::val(ctx,0);
  isl::val One = isl::val(ctx,1);
  PlaceHolder dummy = PlaceHolder(One,Zero,Zero,1);
  // j+1 
  PlaceHolder Inc = PlaceHolder(One, One, Zero,1);
  auto m1 = read('A', dummy, 'B', Inc);
  auto m2 = read('D', dummy, 'B', dummy);
  Scop S = checkScop("inputs/matmul2.c");
  checkReadAndWrite(S);
  std::vector<RelationMatcher> v;
  v.push_back(m1);
  v.push_back(m2);
  Finder f = Finder(S.reads, S.mustWrites, v);
  std::vector<memoryAccess> res;
  res = f.find();
  //printMatches(res);
  EXPECT_TRUE(res.size() == 2);
  int counter = countReadMatched(res);
  EXPECT_TRUE(counter == 2);
  counter = countWriteMatched(res);
  EXPECT_TRUE(counter == 0);
  isl_ctx_free(ctx.release());
  // new test do not match j+1
  // due to placeholder cond.
  auto m3 = read('A', dummy, 'B', dummy);
  auto m4 = read('D', dummy, 'B', dummy);
  std::vector<RelationMatcher> vv;
  vv.push_back(m3);
  vv.push_back(m4);
  Finder ff = Finder(S.reads, S.mustWrites, vv);
  std::vector<memoryAccess> ress;
  ress = ff.find();
  //printMatches(ress);
  EXPECT_TRUE(ress.size() == 1);
}

TEST(AccessMatcher, matmul3) {
  using namespace matchers;
  auto ctx = isl::ctx(isl_ctx_alloc());

  isl::val Zero = isl::val(ctx,0);
  isl::val One = isl::val(ctx,1);
  PlaceHolder dummy = PlaceHolder(One, Zero, Zero, 1);
  // j+1
  PlaceHolder Inc = PlaceHolder(One, One, Zero, 1);
  auto m1 = read('A', dummy, 'B', Inc);
  auto m2 = read('D', dummy, 'B', Inc);
  Scop S = checkScop("inputs/matmul3.c");
  checkReadAndWrite(S);
  std::vector<RelationMatcher> v;
  v.push_back(m1);
  v.push_back(m2);
  Finder f = Finder(S.reads, S.mustWrites, v);
  std::vector<memoryAccess> res;
  res = f.find();
  //printMatches(res);
  EXPECT_TRUE(res.size() == 2);
}

TEST(AccessMatcher, matmul4) {
  using namespace matchers;
  auto ctx = isl::ctx(isl_ctx_alloc());
  
  isl::val Zero = isl::val(ctx,0);
  isl::val One = isl::val(ctx,1);
  isl::val Two = isl::val(ctx,2);
  PlaceHolder dummy = PlaceHolder(One, Zero, Zero, 1);
  // j+1
  PlaceHolder Inc = PlaceHolder(One, One, Zero, 1);
  // 2i
  PlaceHolder Coeff = PlaceHolder(Two, Zero, Zero, 1);
  auto m1 = write('A', Coeff, 'B', Inc);
  auto m2 = read('A', Coeff, 'D', dummy);
  Scop S = checkScop("inputs/matmul4.c");
  checkReadAndWrite(S);
  std::vector<RelationMatcher> v;
  v.push_back(m1);
  v.push_back(m2);
  Finder f = Finder(S.reads, S.mustWrites, v);
  std::vector<memoryAccess> res;
  res = f.find();
  //printMatches(res);
  EXPECT_TRUE(res.size() == 2);
  int counter = countWriteMatched(res);
  EXPECT_TRUE(counter == 1);
}
*/

TEST(AccessMatcher, stencil) {
  using namespace matchers;
  auto ctx = isl::ctx(isl_ctx_alloc());
  Scop S = checkScop("inputs/stencil.c");
  //S.dump();
  isl::val Zero = isl::val(ctx,0);
  isl::val One = isl::val(ctx,1);
  PlaceHolder dummy = PlaceHolder(One, Zero, Zero, 1);
  auto m1 = write('A', dummy);
  auto m2 = read('A', dummy);
  std::vector<RelationMatcher> v;
  v.push_back(m1);
  v.push_back(m2);
  Finder f = Finder(S.reads, S.mustWrites, v);
  std::vector<memoryAccess> res;
  res = f.find();
  printMatches(res);
}
   
int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
