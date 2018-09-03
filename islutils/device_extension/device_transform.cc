//#include <islutils/builders.h>
//#include <islutils/matchers.h>
#include "device_transform.h"
#include "dependency.h"
#include "pet.h"
#include <islutils/parser.h>
#include <string>
#include <vector>

std::unordered_multimap<std::string, std::string> DeviceContext::annotationMap;
using namespace matchers;
// clang-format off
std::vector<ScheduleNodeMatcher> DeviceContext::matchers1d =
    {band(
       anyTree())};
std::vector<ScheduleNodeMatcher> DeviceContext::matchers2d =
    {band(
       band(
         anyTree()))};
std::vector<ScheduleNodeMatcher> DeviceContext::matchers3d =
     {band(
        band(
         band(
	   anyTree())))};
// clang-format on
std::vector<ScheduleNodeMatcher> DeviceContext::matchersMored;
std::vector<PlaceholderSet<StrideCandidate, StridePattern>>
    DeviceContext::accessMatchers;

std::vector<UnpositionedPlaceholder<StrideCandidate, StridePattern>>
    DeviceContext::stridePlaceholderCollection;

static char *concat(isl_ctx *ctx, const char *a, const char *b) {
  isl_printer *p;
  char *s;

  p = isl_printer_to_str(ctx);
  p = isl_printer_print_str(p, a);
  p = isl_printer_print_str(p, "_");
  p = isl_printer_print_str(p, b);
  s = isl_printer_get_str(p);
  isl_printer_free(p);

  return s;
}

static bool isKernel(isl::schedule_node node) {
  if (isl_schedule_node_get_type(node.get()) == isl_schedule_node_band &&
      isl_schedule_node_band_member_get_coincident(node.get(), 0)) {
    return true;
  }
  return false;
}

template <class... Args>
static void annotateStatement(std::string st, Args... args) {
  std::string annotation = strAnnotation(args...);
  DeviceContext::annotationMap.insert({st, annotation});
}

static isl_union_map *createCopyNode(bool direction, isl_union_set *setCopy,
                                     isl_schedule_node *node,
                                     DeviceContext *context) {

  isl_union_set_list *filters;
  filters = isl_union_set_list_alloc(context->ctx_, 0);

  for (int i = 0; i < context->petScop_->n_array; ++i) {
    isl_space *space;
    isl_set *accessed_i;
    int empty;
    const char *name;
    const char *array_name;
    isl_id *id;
    isl_union_set *uset;
    struct pet_array *pa = context->petScop_->arrays[i];

    space = isl_set_get_space(pa->extent);

    accessed_i = isl_union_set_extract_set(setCopy, space);

    empty = isl_set_plain_is_empty(accessed_i);

    if (empty)
      continue;

    if (empty < 0)
      break;

    array_name = isl_set_get_tuple_name(pa->extent);
    name = concat(context->ctx_, direction ? "to_device" : "from_device",
                  array_name);
    id = name ? isl_id_alloc(context->ctx_, name, pa) : NULL;

    space = isl_space_set_alloc(context->ctx_, 0, 0);
    space = isl_space_set_tuple_id(space, isl_dim_set, id);
    uset = isl_union_set_from_set(isl_set_universe(space));
    filters = isl_union_set_list_add(filters, uset);
  }

  isl::schedule_node cpp_node = isl::manage(node);
  cpp_node = cpp_node.child(0);

  isl_union_set *all =
      isl_union_set_list_union(isl_union_set_list_copy(filters));
  int depth = isl_schedule_node_get_schedule_depth(cpp_node.copy());
  auto space = depth < 0 ? NULL : isl_space_set_alloc(context->ctx_, 0, 0);
  isl_union_set *domain = isl_union_set_from_set(isl_set_universe(space));

  isl_union_map *extension = isl_union_map_from_domain_and_range(domain, all);

  return extension;
}

/* ATTENTION: following couple of functions will be deleted soon
   they are used only for debugging */

static std::tuple<isl_union_map *, isl_union_set *, isl_multi_union_pw_aff *>
generateCopyScheduleClean(DeviceContext *context, bool forward, int array_num) {
  // TODO add ability to copy as many arrays as possible
  // or always match for exact number of arrays
  struct pet_array *pa = context->petScop_->arrays[array_num];
  isl_multi_pw_aff *mpa;
  isl_multi_union_pw_aff *mupa;

  isl_space *space = isl_set_get_space(pa->extent);
  space = isl_space_from_range(space);
  space = isl_space_add_dims(space, isl_dim_in, 0);
  space = isl_space_wrap(space);
  space = isl_space_map_from_set(space);
  isl_id *id = isl_id_alloc(context->ctx_, forward ? "read" : "write", nullptr);
  space = isl_space_set_tuple_id(space, isl_dim_in, id);
  space = isl_space_domain(space);

  space = isl_space_map_from_set(space);
  mpa = isl_multi_pw_aff_identity(space);
  mpa = isl_multi_pw_aff_range_factor_range(mpa);
  mupa = isl_multi_union_pw_aff_from_multi_pw_aff(mpa);

  isl_union_map *access = isl_union_map_copy(context->s_->reads.get());
  printf("DUMP READ ACCESS\n");
  isl_union_map_dump(access);
  isl_union_set *range = isl_union_map_range(access);

  isl_map *extentMap = isl_map_from_range(isl_set_copy(pa->extent));
  isl_union_map *extentUnionMap = isl_union_map_from_map(extentMap);

  isl_union_map *intersection = isl_union_map_intersect_range(
      isl_union_map_copy(extentUnionMap), isl_union_set_copy(range));
  isl_union_set *wrapped_union_map = isl_union_map_wrap(intersection);

  isl_union_map *union_wrapped_map_from_set =
      isl_union_map_from_range(wrapped_union_map);

  isl_map *wrapped_map_from_set =
      isl_map_from_union_map(union_wrapped_map_from_set);
  wrapped_map_from_set =
      isl_map_set_tuple_id(wrapped_map_from_set, isl_dim_out, id);

  isl_union_map *final_map = isl_union_map_from_map(wrapped_map_from_set);

  isl_union_set *filter = isl_union_map_range(isl_union_map_copy(final_map));
  filter = isl_union_set_coalesce(filter);

  printf("DUMP END FILTER\n");
  isl_union_set_dump(filter);
  isl_union_set *domain = isl_union_map_range(final_map);
  access = isl_union_set_wrapped_domain_map(domain);
  access = isl_union_map_reverse(access);
  access = isl_union_map_coalesce(access);

  return std::make_tuple(access, filter, mupa);
}

static isl::schedule_node transform(int i, isl_schedule_node *node,
                                    DeviceContext *context) {
  // 1) Match and transform for kernel code

  // 2) Basic transformation
  // Match for :
  // mark (isKernel,
  //   filter(
  //     band(
  //       leaf())))

  // Change THIS part to :
  // kernelAnnotation() -> mark node ?
  // toDeviceAnnotation(DDRMapping) -> definitely not a mark node
  // extension(fromDevice, toDevice
  //   sequence(
  //     filter(toDevice
  //       leaf()))
  //     filter(<the same>
  //       extensionAnnotation() -> mark node ?
  //       extension(readArray, writeArray
  //         sequence(
  //           filter(readArray
  //             scheduleAnnotation() -> mark node ?
  //               band(partialScheduleCopy()
  //                 leaf()))
  //           filter(<the same>
  //             scheduleAnnotation() -> mark node ?
  //               band(<the same>
  //                leaf()))
  //           filter(writeArray
  //             scheduleAnnotation() -> mark node ?
  //             band(partialScheduleCopy()
  //               leaf()))
  //      filter(fromDevice
  //        leaf())
  //   )
  // )

  // 2) Determine the list of what we want to copy
  isl_union_set_list *listToTransfer =
      isl_union_set_list_alloc(context->ctx_, 0);
  isl_union_set *readSet =
      isl_union_map_range(isl_union_map_copy(context->s_->reads.copy()));
  isl_union_set *writeSet =
      isl_union_map_range(isl_union_map_copy(context->s_->mayWrites.copy()));
  listToTransfer = isl_union_set_list_add(listToTransfer, readSet);
  listToTransfer = isl_union_set_list_add(listToTransfer, writeSet);
  isl_union_set *arraysToTransfer =
      isl_union_set_list_union(isl_union_set_list_copy(listToTransfer));
  arraysToTransfer = isl_union_set_detect_equalities(arraysToTransfer);

  /* in this example we copy everything, but don't know the number of arrays,
     so we have arrays for forward and backward copies */
  std::vector<
      std::tuple<isl_union_map *, isl_union_set *, isl_multi_union_pw_aff *>>
      forCopyForwardVector;
  std::vector<
      std::tuple<isl_union_map *, isl_union_set *, isl_multi_union_pw_aff *>>
      forCopyBackwardVector;

  /* we need to union all extensions in one extension node */
  std::vector<isl_union_map *> extensionsArray;

  int problem_size = context->petScop_->n_array;
  for (int i = 0; i < problem_size; i++) {
    forCopyForwardVector.push_back(generateCopyScheduleClean(context, 1, i));
    forCopyBackwardVector.push_back(generateCopyScheduleClean(context, 0, i));
    extensionsArray.push_back(std::get<0>(forCopyForwardVector.at(i)));
    extensionsArray.push_back(std::get<0>(forCopyBackwardVector.at(i)));
  }

  /* transfer from and to device */
  isl_union_map *transferForward = createCopyNode(
      1, arraysToTransfer, isl_schedule_node_copy(node), context);
  isl_union_map *transferBackward = createCopyNode(
      0, arraysToTransfer, isl_schedule_node_copy(node), context);
  isl_union_set *transferForwardFilter =
      isl_union_map_range(isl_union_map_copy(transferForward));
  isl_union_set *transferBackwardFilter =
      isl_union_map_range(isl_union_map_copy(transferBackward));
  isl_union_map *unionTransfer =
      isl_union_map_union(transferForward, transferBackward);

  /* union all extensions */
  isl_union_map *unionCopy = extensionsArray.at(0);
  for (int i = 1; i < problem_size; i++) {
    unionCopy = isl_union_map_union(unionCopy, extensionsArray.at(i));
  }
  isl_union_map *unionExtension = isl_union_map_union(unionTransfer, unionCopy);

  /* collect previous info about band node */
  isl_schedule_node *previousFilterNode =
      isl_schedule_node_parent(isl_schedule_node_copy(node));
  isl::schedule_node cppPreviousFilterNode = isl::manage(previousFilterNode);
  isl_union_set *previousFilter = isl_schedule_node_filter_get_filter(
      isl_schedule_node_copy(previousFilterNode));

  isl_schedule_node *previousBandNode =
      isl_schedule_node_child(isl_schedule_node_copy(node), 0);
  isl_multi_union_pw_aff *previousBandNodeSchedule =
      isl_schedule_node_get_prefix_schedule_multi_union_pw_aff(
          previousBandNode);

  /* union new filters with previous filter */
  isl_union_set *unionFilter = isl_union_set_copy(previousFilter);
  for (int i = 0; i < problem_size; i++) {
    unionFilter = isl_union_set_union(
        unionFilter,
        isl_union_set_copy(std::get<1>(forCopyForwardVector.at(i))));
    unionFilter = isl_union_set_union(
        unionFilter,
        isl_union_set_copy(std::get<1>(forCopyBackwardVector.at(i))));
  }

  std::string kernelName("kernel(" + toString(i) + ")");
  isl_id *id = isl_id_alloc(context->ctx_, kernelName.c_str(), nullptr);

  /* add all annotations */
  annotateStatement("kernel(" + toString(i) + ")", "reqd_work_group_size", 1, 1,
                    1);
  for (int i = 0; i < problem_size; i++) {
    annotateStatement(toString(isl_multi_union_pw_aff_to_str(
                          std::get<2>(forCopyForwardVector.at(i)))),
                      "xcl_pipeline_loop");
    annotateStatement(toString(isl_multi_union_pw_aff_to_str(
                          std::get<2>(forCopyBackwardVector.at(i)))),
                      "xcl_pipeline_loop");
  }
  annotateStatement(
      toString(isl_multi_union_pw_aff_to_str(previousBandNodeSchedule)),
      "xcl_pipeline_loop");
  annotateStatement(
      toString(isl_multi_union_pw_aff_to_str(previousBandNodeSchedule)),
      "xcl_pipeline_loop");

  /*   create cpp objects */
  isl::union_map cppUnionTransfer =
      isl::manage(isl_union_map_copy(unionTransfer));
  isl::union_set cppTransferForwardFilter =
      isl::manage(isl_union_set_copy(transferForwardFilter));
  isl::union_set cppPreviousFilter =
      isl::manage(isl_union_set_copy(previousFilter));
  isl::union_map cppUnionCopy = isl::manage(isl_union_map_copy(unionCopy));

  isl::union_set cppPreviousFilter2 =
      isl::manage(isl_union_set_copy(previousFilter));
  isl::multi_union_pw_aff cppPreviousBandNodeSchedule =
      isl::manage(isl_multi_union_pw_aff_copy(previousBandNodeSchedule));

  isl::union_set cppTransferBackwardFilter =
      isl::manage(isl_union_set_copy(transferBackwardFilter));

  isl::union_map cppUnionExtension =
      isl::manage(isl_union_map_copy(unionExtension));
  isl::union_set cppUnionFilter = isl::manage(isl_union_set_copy(unionFilter));

  isl::id cppId = isl::manage(id);

  std::vector<isl::multi_union_pw_aff> cppCopyForwardScheduleVector;
  std::vector<isl::multi_union_pw_aff> cppCopyBackwardScheduleVector;

  std::vector<isl::union_set> cppCopyForwardSetVector;
  std::vector<isl::union_set> cppCopyBackwardSetVector;

  for (int i = 0; i < problem_size; i++) {
    isl::union_set cppCopyForward1 =
        isl::manage(std::get<1>(forCopyForwardVector.at(i)));
    isl::multi_union_pw_aff cppCopyForward2 =
        isl::manage(std::get<2>(forCopyForwardVector.at(i)));
    isl::union_set cppCopyBackward1 =
        isl::manage(std::get<1>(forCopyBackwardVector.at(i)));
    isl::multi_union_pw_aff cppCopyBackward2 =
        isl::manage(std::get<2>(forCopyBackwardVector.at(i)));
    cppCopyForwardSetVector.push_back(cppCopyForward1);
    cppCopyBackwardSetVector.push_back(cppCopyBackward1);
    cppCopyForwardScheduleVector.push_back(cppCopyForward2);
    cppCopyBackwardScheduleVector.push_back(cppCopyBackward2);
  }

  /* create vector of builders */
  using namespace builders;

  std::vector<ScheduleNodeBuilder> filterForwardVector;
  std::vector<ScheduleNodeBuilder> filterBackwardVector;

  for (int i = 0; i < problem_size; i++) {
    auto builderForward = filter(cppCopyForwardSetVector.at(i),
                                 band(cppCopyForwardScheduleVector.at(i)));
    auto builderBackward = filter(cppCopyBackwardSetVector.at(i),
                                  band(cppCopyBackwardScheduleVector.at(i)));
    filterForwardVector.push_back(builderForward);
    filterBackwardVector.push_back(builderBackward);
  }

  auto builder = mark(
      cppId, extension(cppUnionExtension,
                       sequence(filter(cppTransferForwardFilter),
                                filter(cppUnionFilter,
                                       sequence(filterForwardVector,
                                                subtree(cppPreviousFilterNode),
                                                filterBackwardVector)),
                                filter(cppTransferBackwardFilter))));

  isl_schedule_node *after_cut = isl_schedule_node_cut(node);
  isl::schedule_node cpp_after_cut = isl::manage(after_cut);
  cpp_after_cut = builder.insertAt(cpp_after_cut);

  return cpp_after_cut;
}

static isl_schedule_node *differentiateSchedule(isl_schedule_node *Node,
                                                void *User) {

  DeviceContext *context = static_cast<DeviceContext *>(User);
  // std::vector<isl::schedule_node>* kernel_nodes =
  // static_cast<std::vector<isl::schedule_node>*>(User);
  using namespace matchers;
  auto matcher = band(isKernel, anyTree());

  if (ScheduleNodeMatcher::isMatching(matcher, isl::manage_copy(Node))) {

    isl::schedule_node new_node = transform(
        ++context->matched_nodes_, isl_schedule_node_copy(Node), context);
    return new_node.release();
  }
  return Node;
}

static void dumpAnnotations() {
  printf("\n\n##ANNOTATIONS##\n\n");
  for (auto it = DeviceContext::annotationMap.cbegin();
       it != DeviceContext::annotationMap.cend(); ++it) {
    std::cout << it->second << std::endl;
    std::cout << "\t" << it->first << std::endl;
  }
}

static void initializeAccess(DeviceContext *context) {
  auto ss = stride(context->ctx_, 1);
  DeviceContext::stridePlaceholderCollection.push_back(ss);
  DeviceContext::accessMatchers.push_back(allOf(access(dim(-2, ss))));
}

// unwrapped one binary relation

static isl_union_map *getRangeDomainFromSpaceAccess(isl_space *space) {
  space = isl_space_wrap(space);
  space = isl_space_map_from_set(space);
  isl_multi_pw_aff *mpa = isl_multi_pw_aff_identity(space);
  isl_map *map = isl_map_from_multi_pw_aff(mpa);
  isl_union_map *union_map = isl_union_map_from_map(map);
  isl_union_set *union_set = isl_union_map_range(union_map);
  union_map = isl_union_set_unwrap(union_set);
  return union_map;
}

static std::tuple<isl_union_map *, isl_union_set *, isl_multi_union_pw_aff *>
generateCopyScheduleFromSpace(DeviceContext *context, bool forward,
                              isl_space *inputSpace) {
  printf("INSIDE COPY FROM SPACE\n");
  isl_multi_pw_aff *mpa;
  isl_multi_union_pw_aff *mupa;

  isl_space *space = isl_space_wrap(isl_space_copy(inputSpace));
  space = isl_space_from_range(space);
  space = isl_space_add_dims(space, isl_dim_in, 0);
  space = isl_space_wrap(space);
  space = isl_space_map_from_set(space);
  isl_id *id = isl_id_alloc(context->ctx_, forward ? "read" : "write", nullptr);
  space = isl_space_set_tuple_id(space, isl_dim_in, id);
  space = isl_space_domain(space);

  space = isl_space_map_from_set(space);
  mpa = isl_multi_pw_aff_identity(space);
  mpa = isl_multi_pw_aff_range_factor_range(mpa);
  mpa = isl_multi_pw_aff_range_factor_range(mpa);
  mupa = isl_multi_union_pw_aff_from_multi_pw_aff(mpa);

  isl_union_map *access = isl_union_map_copy(context->s_->reads.get());

  isl_union_set *range = isl_union_map_range(access);

  isl_union_map *input_union_map =
      getRangeDomainFromSpaceAccess(isl_space_copy(inputSpace));

  // isl_union_set_intersect(isl_union_set_copy(range));
  isl_union_map *intersection = isl_union_map_intersect_range(
      isl_union_map_copy(input_union_map), isl_union_set_copy(range));

  isl_union_set *wrapped_union_map = isl_union_map_wrap(intersection);
  isl_union_map *map_from_wrapped_union_map =
      isl_union_map_from_range(wrapped_union_map);

  isl_union_set *wrapped_map_from_wrapped_union_map =
      isl_union_map_wrap(map_from_wrapped_union_map);
  isl_union_map *union_wrapped_map_from_set =
      isl_union_map_from_range(wrapped_map_from_wrapped_union_map);

  isl_map *wrapped_map_from_set =
      isl_map_from_union_map(union_wrapped_map_from_set);
  wrapped_map_from_set =
      isl_map_set_tuple_id(wrapped_map_from_set, isl_dim_out, id);

  isl_union_map *final_map = isl_union_map_from_map(wrapped_map_from_set);

  isl_union_set *filter = isl_union_map_range(isl_union_map_copy(final_map));
  filter = isl_union_set_coalesce(filter);

  isl_union_set *domain = isl_union_map_range(final_map);
  access = isl_union_set_wrapped_domain_map(domain);
  access = isl_union_map_reverse(access);
  access = isl_union_map_coalesce(access);

  printf("DUMP RESULT OF NODE CONSTRUCTION\n");
  isl_union_map_dump(access);
  isl_union_set_dump(filter);
  isl_multi_union_pw_aff_dump(mupa);

  return std::make_tuple(access, filter, mupa);
}

static bool checkFirstCondition(isl_schedule_node *node) {
  printf("INSIDE FIRST CONDITION\n");
  auto matcher = band(isKernel, anyTree());

  if (ScheduleNodeMatcher::isMatching(matcher, isl::manage_copy(node))) {
    return true;
  }
  return false;
}

static std::tuple<bool, ScheduleNodeMatcher, int, int>
checkSecondCondition(DeviceContext *ctx, isl_schedule_node *node) {
  printf("INSIDE SECOND CONDITION\n");
  using namespace matchers;

  ScheduleNodeMatcher dummy = anyTree();

  int i = 0;
  for (ScheduleNodeMatcher m : DeviceContext::matchers1d) {
    if (ScheduleNodeMatcher::isMatching(m, isl::manage_copy(node))) {
      return std::make_tuple(true, m, 1, i);
    }
    i++;
  }

  i = 0;
  for (ScheduleNodeMatcher m : DeviceContext::matchers2d) {
    if (ScheduleNodeMatcher::isMatching(m, isl::manage_copy(node))) {
      return std::make_tuple(true, m, 2, i);
    }
    i++;
  }

  i = 0;
  for (ScheduleNodeMatcher m : DeviceContext::matchers3d) {
    if (ScheduleNodeMatcher::isMatching(m, isl::manage_copy(node))) {
      return std::make_tuple(true, m, 3, i);
    }
    i++;
  }

  // I am not sure yet what to do with 4d

  i = 0;
  for (ScheduleNodeMatcher m : DeviceContext::matchersMored) {
    if (ScheduleNodeMatcher::isMatching(m, isl::manage_copy(node))) {
      return std::make_tuple(false, m, 4, i);
    }
    i++;
  }
  return std::make_tuple(false, anyTree(), 0, 0);
}

static std::vector<isl_space *> checkThirdCondition(DeviceContext *ctx,
                                                    isl_schedule_node *node) {
  std::vector<isl_space *> result;
  printf("INSIDE THIRD CONDITION\n");
  // determine current schedule
  printf("DUMP CURRENT LEAF\n");
  isl_schedule_node_dump(node);
  isl_union_map *schedule =
      isl_schedule_node_get_prefix_schedule_union_map(node);

  // get reads
  isl_union_map *reads = isl_union_map_copy(ctx->s_->reads.get());
  reads = isl_union_map_curry(reads);
  reads = isl_union_map_apply_domain(reads, isl_union_map_copy(schedule));
  isl::union_map cpp_reads = isl::manage(isl_union_map_copy(reads));

  // get writes
  isl_union_map *writes = isl_union_map_copy(ctx->s_->mustWrites.get());
  writes = isl_union_map_curry(writes);
  writes = isl_union_map_apply_domain(writes, isl_union_map_copy(schedule));
  isl::union_map cpp_writes = isl::manage(isl_union_map_copy(writes));

  // dump information
  printf("DUMP READS FOR EXACT NODE\n");
  isl_union_map_dump(reads);
  printf("\n");
  printf("DUMP WRITES FOR EXACT NODE\n");
  isl_union_map_dump(writes);
  printf("\n");

  // check independently reads against all matchers
  int i = 0;
  for (auto am : DeviceContext::accessMatchers) {
    auto matches = match(cpp_reads, am);
    printf("MATCHED SIZE FOR READS: %i\n", matches.size());
    for (auto m : matches) {
      m[DeviceContext::stridePlaceholderCollection.at(i)]
          .candidateMapSpace_.dump();
      isl::space currCppSpace =
          m[DeviceContext::stridePlaceholderCollection.at(i)]
              .candidateMapSpace_;
      isl_space *curr_space = currCppSpace.get();
      curr_space = isl_space_range(curr_space);
      curr_space = isl_space_unwrap(curr_space);
      result.push_back(curr_space);
      // generateCopyScheduleFromSpace(ctx, 1,
      // isl_space_unwrap(isl_space_range(currCppSpace.get())));
    }
    i++;
  }

  /* // check independently writes against all matchers
  i = 0;
  for (auto am : DeviceContext::accessMatchers) {
    auto matches = match(cpp_writes, am);
    printf("MATCHED SIZE FOR WRITES: %i\n", matches.size());
    for (auto m : matches) {
      m[DeviceContext::stridePlaceholderCollection.at(i)].candidateMapSpace_.dump();
      isl::space currCppSpace =
  m[DeviceContext::stridePlaceholderCollection.at(i)].candidateMapSpace_;
      result.push_back(isl_space_unwrap(isl_space_range(currCppSpace.get())));
      generateCopyScheduleFromSpace(ctx, 1,
  isl_space_unwrap(isl_space_range(currCppSpace.get())));
    }
    i++;
    }*/
  return result;
}

/*
 * The strategy here might be changed in future;
 * Initally pass root in the function
 */

static isl_schedule_node *reachLeaf(isl_schedule_node *node) {
  printf("INSIDE REACH LEAF\n");
  // here reach the first leaf
  // maybe we need some checks about type of accesses
  // trivial or not

  isl_schedule_node *leaf = isl_schedule_node_copy(node);
  while (isl_schedule_node_get_type(leaf) != isl_schedule_node_leaf) {
    leaf = isl_schedule_node_child(leaf, 0);
  }

  return leaf;
}

static isl::schedule_node
createFirstTypeBuilder(DeviceContext *context,
                       std::vector<isl_space *> spaceVector,
                       isl_schedule_node *node) {
  isl_union_set_list *listToTransfer =
      isl_union_set_list_alloc(context->ctx_, 0);
  isl_union_set *readSet =
      isl_union_map_range(isl_union_map_copy(context->s_->reads.copy()));
  isl_union_set *writeSet =
      isl_union_map_range(isl_union_map_copy(context->s_->mayWrites.copy()));
  listToTransfer = isl_union_set_list_add(listToTransfer, readSet);
  listToTransfer = isl_union_set_list_add(listToTransfer, writeSet);
  isl_union_set *arraysToTransfer =
      isl_union_set_list_union(isl_union_set_list_copy(listToTransfer));
  arraysToTransfer = isl_union_set_detect_equalities(arraysToTransfer);

  std::vector<
      std::tuple<isl_union_map *, isl_union_set *, isl_multi_union_pw_aff *>>
      forCopyForwardVector;
  std::vector<
      std::tuple<isl_union_map *, isl_union_set *, isl_multi_union_pw_aff *>>
      forCopyBackwardVector;

  /* we need to union all extensions in one extension node */
  std::vector<isl_union_map *> extensionsArray;

  int problem_size = spaceVector.size();
  for (int i = 0; i < problem_size; i++) {
    forCopyForwardVector.push_back(
        generateCopyScheduleFromSpace(context, 1, spaceVector.at(i)));
    forCopyBackwardVector.push_back(
        generateCopyScheduleFromSpace(context, 0, spaceVector.at(i)));
    extensionsArray.push_back(std::get<0>(forCopyForwardVector.at(i)));
    extensionsArray.push_back(std::get<0>(forCopyBackwardVector.at(i)));
  }

  /* transfer from and to device */
  isl_union_map *transferForward = createCopyNode(
      1, arraysToTransfer, isl_schedule_node_copy(node), context);
  isl_union_map *transferBackward = createCopyNode(
      0, arraysToTransfer, isl_schedule_node_copy(node), context);
  isl_union_set *transferForwardFilter =
      isl_union_map_range(isl_union_map_copy(transferForward));
  isl_union_set *transferBackwardFilter =
      isl_union_map_range(isl_union_map_copy(transferBackward));
  isl_union_map *unionTransfer =
      isl_union_map_union(transferForward, transferBackward);

  /* union all extensions */
  isl_union_map *unionCopy = extensionsArray.at(0);
  for (int i = 1; i < problem_size; i++) {
    unionCopy = isl_union_map_union(unionCopy, extensionsArray.at(i));
  }
  isl_union_map *unionExtension = isl_union_map_union(unionTransfer, unionCopy);

  /* collect previous info about band node */
  isl_schedule_node *previousFilterNode =
      isl_schedule_node_parent(isl_schedule_node_copy(node));
  isl::schedule_node cppPreviousFilterNode = isl::manage(previousFilterNode);
  isl_union_set *previousFilter = isl_schedule_node_filter_get_filter(
      isl_schedule_node_copy(previousFilterNode));

  isl_schedule_node *previousBandNode =
      isl_schedule_node_child(isl_schedule_node_copy(node), 0);
  isl_multi_union_pw_aff *previousBandNodeSchedule =
      isl_schedule_node_get_prefix_schedule_multi_union_pw_aff(
          previousBandNode);

  /* union new filters with previous filter */
  isl_union_set *unionFilter = isl_union_set_copy(previousFilter);
  for (int i = 0; i < problem_size; i++) {
    unionFilter = isl_union_set_union(
        unionFilter,
        isl_union_set_copy(std::get<1>(forCopyForwardVector.at(i))));
    unionFilter = isl_union_set_union(
        unionFilter,
        isl_union_set_copy(std::get<1>(forCopyBackwardVector.at(i))));
  }

  // TODO
  std::string kernelName("kernel()");
  isl_id *id = isl_id_alloc(context->ctx_, kernelName.c_str(), nullptr);

  /* add all annotations */
  // annotateStatement("kernel(" + toString(i)+")", "reqd_work_group_size", 1,
  // 1, 1);
  for (int i = 0; i < problem_size; i++) {
    annotateStatement(toString(isl_multi_union_pw_aff_to_str(
                          std::get<2>(forCopyForwardVector.at(i)))),
                      "xcl_pipeline_loop");
    annotateStatement(toString(isl_multi_union_pw_aff_to_str(
                          std::get<2>(forCopyBackwardVector.at(i)))),
                      "xcl_pipeline_loop");
  }
  annotateStatement(
      toString(isl_multi_union_pw_aff_to_str(previousBandNodeSchedule)),
      "xcl_pipeline_loop");
  annotateStatement(
      toString(isl_multi_union_pw_aff_to_str(previousBandNodeSchedule)),
      "xcl_pipeline_loop");

  /*   create cpp objects */
  isl::union_map cppUnionTransfer =
      isl::manage(isl_union_map_copy(unionTransfer));
  isl::union_set cppTransferForwardFilter =
      isl::manage(isl_union_set_copy(transferForwardFilter));
  isl::union_set cppPreviousFilter =
      isl::manage(isl_union_set_copy(previousFilter));
  isl::union_map cppUnionCopy = isl::manage(isl_union_map_copy(unionCopy));

  isl::union_set cppPreviousFilter2 =
      isl::manage(isl_union_set_copy(previousFilter));
  isl::multi_union_pw_aff cppPreviousBandNodeSchedule =
      isl::manage(isl_multi_union_pw_aff_copy(previousBandNodeSchedule));

  isl::union_set cppTransferBackwardFilter =
      isl::manage(isl_union_set_copy(transferBackwardFilter));

  isl::union_map cppUnionExtension =
      isl::manage(isl_union_map_copy(unionExtension));
  isl::union_set cppUnionFilter = isl::manage(isl_union_set_copy(unionFilter));

  isl::id cppId = isl::manage(id);

  std::vector<isl::multi_union_pw_aff> cppCopyForwardScheduleVector;
  std::vector<isl::multi_union_pw_aff> cppCopyBackwardScheduleVector;

  std::vector<isl::union_set> cppCopyForwardSetVector;
  std::vector<isl::union_set> cppCopyBackwardSetVector;

  for (int i = 0; i < problem_size; i++) {
    isl::union_set cppCopyForward1 =
        isl::manage(std::get<1>(forCopyForwardVector.at(i)));
    isl::multi_union_pw_aff cppCopyForward2 =
        isl::manage(std::get<2>(forCopyForwardVector.at(i)));
    isl::union_set cppCopyBackward1 =
        isl::manage(std::get<1>(forCopyBackwardVector.at(i)));
    isl::multi_union_pw_aff cppCopyBackward2 =
        isl::manage(std::get<2>(forCopyBackwardVector.at(i)));
    cppCopyForwardSetVector.push_back(cppCopyForward1);
    cppCopyBackwardSetVector.push_back(cppCopyBackward1);
    cppCopyForwardScheduleVector.push_back(cppCopyForward2);
    cppCopyBackwardScheduleVector.push_back(cppCopyBackward2);
  }

  /* create vector of builders */
  using namespace builders;

  std::vector<ScheduleNodeBuilder> filterForwardVector;
  std::vector<ScheduleNodeBuilder> filterBackwardVector;

  for (int i = 0; i < problem_size; i++) {
    auto builderForward = filter(cppCopyForwardSetVector.at(i),
                                 band(cppCopyForwardScheduleVector.at(i)));
    auto builderBackward = filter(cppCopyBackwardSetVector.at(i),
                                  band(cppCopyBackwardScheduleVector.at(i)));
    filterForwardVector.push_back(builderForward);
    filterBackwardVector.push_back(builderBackward);
  }

  // clang-format off
  auto builder = mark(cppId,
		    extension(cppUnionExtension,
		     sequence(
		       filter(cppTransferForwardFilter),
		       filter(cppUnionFilter,
		       	 sequence(
		           filterForwardVector,
			   subtree(cppPreviousFilterNode),
			   filterBackwardVector
		         )
		       ),
		       filter(cppTransferBackwardFilter)
		     )
		   )
		 );

  // clang-format on

  isl_schedule_node *after_cut = isl_schedule_node_cut(node);
  isl::schedule_node cpp_after_cut = isl::manage(after_cut);
  cpp_after_cut = builder.insertAt(cpp_after_cut);

  return cpp_after_cut;
}

static isl_schedule_node *findAndReplaceDevice(DeviceContext *ctx,
                                               isl_schedule_node *node) {
  // check conditions (1)
  printf("DUMP OUR CURRENT POSITION\n");
  isl_schedule_node_dump(node);
  bool firstResult = checkFirstCondition(node);
  printf("FIRST RESULT : %i\n", firstResult);
  // proceed to the next node if does not match
  // (perhaps not deeper than on two nodes)

  if (!firstResult) {
    size_t nChildren = static_cast<size_t>(isl_schedule_node_n_children(node));
    for (size_t i = 0; i < nChildren; ++i) {
      isl_schedule_node *child =
          isl_schedule_node_child(isl_schedule_node_copy(node), i);
      node = isl_schedule_node_parent(findAndReplaceDevice(ctx, child));
      return node;
    }
  }

  // check conditions (2)
  auto secondResult = checkSecondCondition(ctx, node);
  printf("SECOND RESULT : %i\n", std::get<0>(secondResult));
  // return to the previous node if does not match
  if (!std::get<0>(secondResult)) {
    return node;
  }
  // third condition is connected with accesses,
  // so go to leaf first,
  // for now check only in one leaf (not sure what to do if there are many of
  // them)

  isl_schedule_node *leaf = reachLeaf(node);
  printf("DUMP LEAF POSITION\n");
  isl_schedule_node_dump(leaf);
  // check conditions (3)
  std::vector<isl_space *> thirdResult = checkThirdCondition(ctx, leaf);
  printf("DUMP RESULT VECTOR\n");
  for (isl_space *sp : thirdResult) {
    isl_space_dump(sp);
    printf("\n");
  }
  if (thirdResult.size() != 0) {
    isl::schedule_node new_node =
        createFirstTypeBuilder(ctx, thirdResult, isl_schedule_node_copy(node));
    printf("DUMP RESULT NODE\n");
    new_node.dump();
    return new_node.release();
  } else {
    return node;
  }
  printf("THIRD RESULT : %i\n", thirdResult);
  return node;
}

void runAllFlow(std::string fileName, bool computeSchedule) {

  std::vector<isl::schedule_node> kernel_nodes;
  Scop S = Parser(fileName).getScop();

  /* to test the access ranges */

  //  isl_union_map *access = isl_union_map_copy(S.reads.get());
  // isl_union_set* range = isl_union_map_range(access);
  // printf("range of read accesses before reschedule\n");
  // isl_union_set_dump(range);

  // printf("\ndump all schedule\n\n");
  // isl_schedule_node* oldNode = isl_schedule_get_root(S.schedule.get());
  // isl_schedule_node_dump(oldNode);
  /*----*/

  pet_scop *scop_pet = pet_scop_extract_from_C_source(
      S.mustWrites.get_ctx().get(), fileName.c_str(), NULL);
  /* construct common info Class*/

  isl_schedule_node_dump(isl_schedule_get_root(S.schedule.get()));
  DeviceContext *context =
      new DeviceContext(&S, scop_pet, fileName, S.mustWrites.get_ctx().get());
  /* set options */
  isl_options_set_ast_build_detect_min_max(S.mustWrites.get_ctx().get(), 1);
  isl_options_set_ast_print_macro_once(S.mustWrites.get_ctx().get(), 1);
  isl_options_set_schedule_whole_component(S.mustWrites.get_ctx().get(), 0);
  isl_options_set_schedule_maximize_band_depth(S.mustWrites.get_ctx().get(), 1);
  isl_options_set_schedule_maximize_coincidence(S.mustWrites.get_ctx().get(),
                                                1);
  isl_options_set_schedule_serialize_sccs(S.mustWrites.get_ctx().get(), 0);
  isl_options_set_schedule_outer_coincidence(S.mustWrites.get_ctx().get(), 1);

  /* initialize access matchers */
  initializeAccess(context);

  /* compute flow and dependencies */

  compute_dependencies(&S);

  /* compute schedule constraints */
  isl_schedule_constraints *sc;
  isl_union_map *validity, *coincidence, *proximity;
  isl_union_map *dep_raw, *dep;
  isl_schedule *new_schedule;

  sc = compute_schedule_constraints(sc, validity, coincidence, dep_raw, dep,
                                    proximity, &S);
  new_schedule = isl_schedule_constraints_compute_schedule(sc);

  isl_schedule_node *node = isl_schedule_get_root(new_schedule);
  isl_schedule_node_dump(node);

  /* temporal solution to track number of kernels */

  /*    context->matched_nodes_ = 0;
   node = isl_schedule_node_map_descendant_bottom_up(node,
   differentiateSchedule, (static_cast<void *>(context)));
                                               isl_schedule_node_dump(node);*/
  // dumpAnnotations();
  // we should remember to mark our extrension nodes to transfer to device wuith
  // different ddr banks

  node = findAndReplaceDevice(context, node);
  printf("CHECK IF RETURNED NODE IS ROOT\n");
  isl_schedule_node_dump(node);
}
