#ifndef TEST_EXTENSION_H
#define TEST_EXTENSION_H
#include <islutils/scop.h>
#include "pet.h"
#include <vector>
#include <unordered_map>
#include <sstream>
typedef std::string matchers_annotations;

class TestContext {
public:
  Scop* s_;
  pet_scop* petScop_;
  std::string fileName_;
  isl_ctx* ctx_;
  std::vector<isl_schedule_node*> matched_nodes_;

  // for host/kernel purpose special flag
  // the vector is supposed to contain all currently matched nodes
  // kernel1 -> <...>
  // local_A -> <...>
  //std::unordered_multimap<std::string, std::string> annotationMap;
  
  TestContext(Scop* s, pet_scop* petScop, std::string fileName, isl_ctx* ctx)
  :s_(s), petScop_(petScop), fileName_(fileName), ctx_(ctx) 
  {
  }
};

enum statementType {
  function,
  declaration,
  loop
};

enum annotationType {
  dataflow,
  groupsize,
  pipeline,
  unroll,
  partition,
  reshape
};

std::string annotationNames[] = {"dataflow", "groupsize", "pipeline", "reshape", "partition", "reshape"};

template <typename T>
std::string toString(const T& value) {
	std::stringstream ss;
	ss << value;
	return ss.str();
}

template<class ... Args>
std::string strAnnotation(Args... args) {
  std::string result = "__attribute__((";
  auto argSize =  sizeof...(args);
  int i = 0;
  for (const auto& p : { toString(args)... }) {
    result.append(p);
    if (!i && argSize >= 2) result.append("(");
    if (i > 0 && i != (argSize - 1)) result.append(", ");
    i += 1;
  }

  if (argSize >= 2) result.append(")");
  result.append("))");
  return result;
}

class Statement {
  statementType type;
  std::string name;
  
  std::string toString() {
    
  }
  //no idea what it should be currently
};

std::unordered_multimap<std::string, std::string> annotationMap;

#endif TEST_EXTENSION_H
