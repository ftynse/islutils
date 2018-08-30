#ifndef BUILDERS_H
#define BUILDERS_H

#include <isl/cpp.h>
#include <isl/id.h>

#include <vector>

namespace builders {

class ScheduleNodeBuilder {
private:
  isl_union_set_list *collectChildFilters(isl::ctx) const;
  isl::schedule_node insertSequenceOrSetAt(isl::schedule_node,
                                           isl_schedule_node_type type) const;
  isl::schedule_node
  insertSingleChildTypeNodeAt(isl::schedule_node,
                              isl_schedule_node_type type) const;

  isl::schedule_node expandTree(isl::schedule_node) const;

public:
  isl::schedule_node insertAt(isl::schedule_node node) const;
  isl::schedule_node build() const;

public:
  isl_schedule_node_type current_;
  std::vector<ScheduleNodeBuilder> children_;

  // XXX: Cannot use a union because C++ isl types have non-trivial
  // constructors.
  isl::set set_;
  isl::union_set uset_;
  isl::multi_union_pw_aff mupa_;
  isl::union_map umap_;

  isl::union_pw_multi_aff upma_;
  isl::id id_;
};

ScheduleNodeBuilder domain(isl::union_set uset);
ScheduleNodeBuilder domain(isl::union_set uset, ScheduleNodeBuilder &&child);

ScheduleNodeBuilder band(isl::multi_union_pw_aff mupa);
ScheduleNodeBuilder band(isl::multi_union_pw_aff mupa,
                         ScheduleNodeBuilder &&child);

ScheduleNodeBuilder filter(isl::union_set uset);
ScheduleNodeBuilder filter(isl::union_set uset, ScheduleNodeBuilder &&child);

ScheduleNodeBuilder extension(isl::union_map umap);
ScheduleNodeBuilder extension(isl::union_map umap, ScheduleNodeBuilder &&child);

ScheduleNodeBuilder expansion(isl::union_map expansion);
ScheduleNodeBuilder expansion(isl::union_map expansion,
                              ScheduleNodeBuilder &&child);

ScheduleNodeBuilder mark(isl::id id);
ScheduleNodeBuilder mark(isl::id id, ScheduleNodeBuilder &&child);

ScheduleNodeBuilder guard(isl::set set);
ScheduleNodeBuilder guard(isl::set set, ScheduleNodeBuilder &&child);

ScheduleNodeBuilder context(isl::set set);
ScheduleNodeBuilder context(isl::set set, ScheduleNodeBuilder &&child);

template <typename... Args, typename = typename std::enable_if<std::is_same<
                                typename std::common_type<Args...>::type,
                                ScheduleNodeBuilder>::value>::type>
ScheduleNodeBuilder sequence(Args... children) {
  ScheduleNodeBuilder builder;
  builder.current_ = isl_schedule_node_sequence;
  builder.children_ = {children...};
  return builder;
}

ScheduleNodeBuilder sequence(std::vector<ScheduleNodeBuilder> &&children);

template <typename... Args, typename = typename std::enable_if<std::is_same<
                                typename std::common_type<Args...>::type,
                                ScheduleNodeBuilder>::value>::type>
ScheduleNodeBuilder set(Args... children) {
  ScheduleNodeBuilder builder;
  builder.current_ = isl_schedule_node_set;
  builder.children_ = {children...};
  return builder;
}

ScheduleNodeBuilder set(std::vector<ScheduleNodeBuilder> &&children);

ScheduleNodeBuilder subtree(isl::schedule_node node);

template <typename T>
std::vector<ScheduleNodeBuilder> sequenceTransform(T t) {
  return {t};
}

template<typename T, class ...Args>
std::vector<ScheduleNodeBuilder> sequenceTransform(T t, Args... args)
{

   if (sizeof...(args) == 0) {
     return sequenceTransform(t);
   }
   std::vector<ScheduleNodeBuilder> vv = sequenceTransform(args...);
   std::vector<ScheduleNodeBuilder> vv2 = {t};
   vv2.insert(std::end(vv2), std::begin(vv), std::end(vv));;
   return vv2;
}

template<class ...Args>
ScheduleNodeBuilder sequence(Args... args) {
  std::vector<ScheduleNodeBuilder> children = sequenceTransform(args...);
  ScheduleNodeBuilder builder;
  builder.current_ = isl_schedule_node_sequence;
  builder.children_ = children;
  return builder;
}


} // namespace builders

#endif // BUILDERS_H
