#include <islutils/builders.h>
#include <islutils/matchers.h>
#include <islutils/parser.h>
#include <iostream>

#include "gtest/gtest.h"

TEST(TreeMatcher, ReadFromFile) {
  Scop S = Parser("inputs/one-dimensional-init.c").getScop();
  EXPECT_TRUE(!S.schedule.is_null());
}

TEST(TreeMatcher, CompileTest) {
  using namespace matchers;

  // clang-format off
  auto matcher =
      domain(
        context(
          sequence(
            band(
              leaf()),
            band(
              leaf()),
            filter(
              any()))));
  // clang-format on
  auto m2 = sequence(any());
  auto m3 = sequence(filter(any()), filter(any()));
  auto m4 = sequence([](isl::schedule_node n) { return true; }, any());
  auto m5 = sequence([](isl::schedule_node n) { return true; }, filter(leaf()),
                     filter(leaf()));

  auto m6 = sequence(filter(hasNextSibling(filter(any())), any()));
  auto m7 = sequence(filter(
      hasNextSibling(filter(hasPreviousSibling(filter(any())), any())), any()));
  auto m8 = sequence(filter(hasSibling(filter(any())), any()));

  auto m9 = sequence(hasDescendant(band(leaf())), any());
  auto m10 = band(leaf());
  auto m11 = band([](isl::schedule_node n) { return true; }, leaf());

  // access pattern matchers.
  auto m12 = read('X');
  auto m13 = read('X', 'Y');
  auto m14 = write('Z');
  auto m15 = write('S', 'Y');
}

static isl::schedule_node makeGemmTree() {
  using namespace builders;
  auto ctx = isl::ctx(isl_ctx_alloc());
  auto iterationDomain = isl::union_set(
      ctx, "{S1[i,j]: 0 <= i,j < 10; S2[i,j,k]: 0 <= i,j,k < 42}");
  auto sched =
      isl::multi_union_pw_aff(ctx, "[{S1[i,j]->[(i)]; S2[i,j]->[(i)]}, "
                                   "{S1[i,j]->[(j)]; S2[i,j]->[(j)]}]");
  auto filterS1 = isl::union_set(ctx, "{S1[i,j]}");
  auto filterS2 = isl::union_set(ctx, "{S2[i,j]}");
  auto innerSched = isl::multi_union_pw_aff(ctx, "[{S2[i,j,k]->[(k)]}]");

  // clang-format off
  auto builder =
    domain(iterationDomain,
      band(sched,
        sequence(
          filter(filterS1),
          filter(filterS2,
            band(innerSched)))));
  // clang-format on

  return builder.build();
}

TEST(TreeMatcher, AnyMatchesLeaf) {
  using namespace matchers;
  // clang-format off
  auto matcher =
    band(
      sequence(
        filter(
          leaf()),
        filter(
          band(any()))));
  // clang-format on

  auto node = makeGemmTree();
  EXPECT_TRUE(ScheduleNodeMatcher::isMatching(matcher, node.child(0)));
}

TEST(TreeMatcher, LeafMatchesLeaf) {
  using namespace matchers;
  // clang-format off
  auto matcher =
    band(
      sequence(
        filter(
          leaf()),
        filter(
          band(
            leaf()))));
  // clang-format on

  auto node = makeGemmTree();
  EXPECT_TRUE(ScheduleNodeMatcher::isMatching(matcher, node.child(0)));
}

//debug helpers.

// helper function for printing single constraint.
inline void print_single_constraint(std::ostream &OS,
                                    const constraints::singleConstraint &c) {
  OS << std::get<0>(c) << "," << std::get<1>(c).to_str();
}

// overloading << for printing single constraint.
inline auto& operator<<(std::ostream &OS, const constraints::singleConstraint &c) {
  OS << "(";
  print_single_constraint(OS, c);
  return OS << ")";
}

// helper function for multiple constraints.
inline void print_multiple_constraints(std::ostream &OS,
				       const constraints::MultipleConstraints &mc) {
  for(std::size_t i = 0; i < mc.size()-1; ++i) {
    OS << mc[i] << ",";
  }
  OS << mc[mc.size()-1];
}

// overloading << for multiple constraints.
inline auto& operator<<(std::ostream &OS, const constraints::MultipleConstraints &mc) {
  OS << "[";
  print_multiple_constraints(OS, mc);
  return OS << "]";
}

// overloading << for ConstraintsList
inline auto& operator<<(std::ostream &OS, const constraints::ConstraintsList &mc) {
  OS << "{";
  OS << "\n";
  OS << "Involved Dims = " << mc.dimsInvolved << "\n";
  if(mc.dimsInvolved == -1) {
    OS << "Constraints = empty";
    OS << "\n";
    return OS << "}";
  }
  OS << "Constraints = " << mc.constraints;
  OS << "\n";
  return OS << "}";
}

// overloading of << to print the entire structure of
// a matchers.
inline auto& operator<<(std::ostream &OS, const matchers::RelationMatcher &m) {
  OS << "@@@@@@\n";
  switch(m.getType()) {
  case 0:
    OS << "Read matcher\n";
    break;
  case 1:
    OS << "Write matcher\n";
    break;
  case 2:
    OS << "Read & Write matcher\n";
  default:
    OS << "NA\n";
  }
  int n_labels = m.getIndexesSize();
  for(int i=0; i<n_labels; ++i) {
    OS << m.getIndex(i) << "\n";
  }
  for(int i=0; i<n_labels; ++i){
    auto payload = m.getDims(i);
    for(size_t j=0; j<payload.size(); ++j) {
      OS << payload[j].to_str() << "\n";
    }
  }
  return OS << "@@@@@@\n";
}

// overloading of << to print std::vector<isl::map>
inline auto& operator<<(std::ostream &OS, const std::vector<isl::map> &v) {
  for(size_t i=0; i<v.size(); ++i) {
    OS << v[i].to_str() << "\n";
  }
  return OS << "\n";
}
//end debug helpers

TEST(TreeMatcher, matmul) {

/*
  // inputs/matmul.c
  #pragma scop
  for(int i=0; i<N; ++i)
    for(int j=0; j<N; ++j) {
      C[i][j] = 0;
      for(int k=0; k<N; ++k)
        C[i][j] += B[k][j] * A[i][k];
    }
  #pragma endscop
*/

  using namespace matchers;
  using namespace constraints;
  std::cout << "matmul test" << std::endl;
  Scop S = Parser("inputs/matmul.c").getScop();
  auto A = read('X','Y');
  auto B = read('Y', 'Z');
  //S.dump();
  
  auto listA = buildMatcherConstraintsReads(A,S.reads);
  //std::cout << "listA" << listA << std::endl;
  auto listB = buildMatcherConstraintsReads(B,S.reads);
  //std::cout << "listB" << listB << std::endl;
  auto listRes = compareLists(listA, listB);
  //std::cout << "listRes" << listRes << std::endl;

  A.setDims(listRes.constraints);
  B.setDims(listRes.constraints);
  //std::cout << A << std::endl;
  //std::cout << B << std::endl;
  
  auto resA = A.getAccesses(S.reads);
  //std::cout << resA << std::endl;
  auto resB = B.getAccesses(S.reads);
  //std::cout << resB << std::endl;
  EXPECT_TRUE((resA.size() == 1)&&(resB.size()==1));

  auto C = read('X','Y');
  auto D = read('X','Z');
  auto listC = buildMatcherConstraintsReads(C,S.reads);
  auto listD = buildMatcherConstraintsReads(D,S.reads);
  auto listRess = compareLists(listC, listD);
  C.setDims(listRess.constraints);
  D.setDims(listRess.constraints);
  auto resC = C.getAccesses(S.reads);
  auto resD = D.getAccesses(S.reads);
  std::cout << resC << std::endl;
  std::cout << resD << std::endl;
  EXPECT_TRUE((resD.size() == 1)&&(resC.size()==1));
}

TEST(TreeMatcher, transpose) {
  using namespace matchers;
  using namespace constraints;
  //std::cout << "transpose test" << std::endl;
  //Scop S = Parser("inputs/transpose.c").getScop();
  
  auto A = read('X','Y');
  auto B = read('Y','X');

  //auto listA = buildMatcherConstraintsReads(A,S.reads);
  //auto listB = buildMatcherConstraintsReads(B,S.reads);
  //auto lisRes = compareLists(listA, listB);
}
   
int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
