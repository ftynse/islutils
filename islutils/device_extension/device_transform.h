#ifndef DEVICE_TRANSFORM_H
#define DEVICE_TRANSFORM_H
#include "islutils/access.h"
#include "islutils/access_patterns.h"
#include "islutils/ctx.h"
#include "islutils/parser.h"

#include "pet.h"
#include <islutils/builders.h>
#include <islutils/matchers.h>
#include <islutils/scop.h>
#include <sstream>
#include <unordered_map>
#include <vector>
typedef std::string matchers_annotations;

class DeviceContext {
public:
  Scop *s_;
  pet_scop *petScop_;
  std::string fileName_;
  isl_ctx *ctx_;
  int matched_nodes_;
  // std::unordered_multimap<std::string, std::string> annotationMap;

  DeviceContext(Scop *s, pet_scop *petScop, std::string fileName, isl_ctx *ctx)
      : s_(s), petScop_(petScop), fileName_(fileName), ctx_(ctx) {}
  static std::unordered_multimap<std::string, std::string> annotationMap;
  static std::vector<matchers::ScheduleNodeMatcher> matchers1d;
  static std::vector<matchers::ScheduleNodeMatcher> matchers2d;
  static std::vector<matchers::ScheduleNodeMatcher> matchers3d;
  static std::vector<matchers::ScheduleNodeMatcher> matchersMored;
  static std::vector<matchers::PlaceholderSet<matchers::StrideCandidate,
                                              matchers::StridePattern>>
      accessMatchers;

  static std::vector<matchers::UnpositionedPlaceholder<
      matchers::StrideCandidate, matchers::StridePattern>>
      stridePlaceholderCollection;
};

enum statementType { function, declaration, loop };

enum annotationType {
  dataflow,
  groupsize,
  pipeline,
  unroll,
  partition,
  reshape
};

// std::string annotationNames[] = {"dataflow", "groupsize", "pipeline",
// "reshape", "partition", "reshape"};

template <typename T> std::string toString(const T &value) {
  std::stringstream ss;
  ss << value;
  return ss.str();
}

template <class... Args> std::string strAnnotation(Args... args) {
  std::string result = "__attribute__((";
  auto argSize = sizeof...(args);
  int i = 0;
  for (const auto &p : {toString(args)...}) {
    result.append(p);
    if (!i && argSize >= 2)
      result.append("(");
    if (i > 0 && i != (argSize - 1))
      result.append(", ");
    i += 1;
  }

  if (argSize >= 2)
    result.append(")");
  result.append("))");
  return result;
}

class Statement {
  statementType type;
  std::string name;

  std::string toString() { return "true"; }
  // no idea what it should be currently
};

void runAllFlow(std::string fileName, bool computeSchedule);

#endif // DEVICE_TRANSFORM_H
