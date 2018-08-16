#include "islutils/matchers.h"
#include <iostream>
using namespace std;

namespace matchers {

// build a placeholder.
// A placeholder represents a dimension and it is used
// to check some properties on the dimension itself.
PlaceHolder::PlaceHolder(isl::val c, isl::val i, isl::val s, int o) {
  assert(o == 1 && "for now only single dim");
  assert(!c.is_zero() && "zero coeff not allowed");
  assert(c.is_pos() && "non positive coeff not allowed");
  this->coefficient_ = c;
  this->increment_ = i;
  this->stride_ = s;
  this->outDimPos_ = o;
} 

// modify the coefficient value if the placeholder
void PlaceHolder::setCoefficient(isl::val c) {
  assert(!c.is_zero() && "zero coeff not allowed");
  assert(c.is_pos() && "non positive coeff not allowed");
  this->coefficient_ = c;
}

// modify the increment value in the placeholder
void PlaceHolder::setIncrement(isl::val i) {
  this->increment_ = i;
}

// modify the stride in the placeholder
void PlaceHolder::setStride(isl::val s) {
  this->stride_ = s;
}

// modify the number of dimension in the placeholder.
void PlaceHolder::setOutDimPos(int o) {
  this->outDimPos_ = o;
}

// set the dimensions for the current matcher.
void RelationMatcher::setDims(constraints::MultipleConstraints &mc) {
  std::vector<isl::pw_aff> tmp;
  for(std::size_t i=0; i<indexes_.size(); ++i) {
    for(std::size_t j=0; j<mc.size(); ++j) {
      if(indexes_[i] == std::get<0>(mc[j])) {
        tmp.push_back(std::get<1>(mc[j]));
      }
    }
    setDim_.push_back(tmp);
    //std::cout << "[setDims] Index" << indexes_[i] << std::endl;
    //std::cout << "[setDims]" << tmp << std::endl;
    tmp.erase(tmp.begin(), tmp.end());
  }
}

// is (are) the dimension(s) set?
bool RelationMatcher::isSet() const {
  return isSetDim_;
}

// set flag for dims.
void RelationMatcher::set() {
  isSetDim_ = true;
}

// returns the number of literals assigned to the matcher.
unsigned RelationMatcher::getIndexesSize() const {
  return indexes_.size();
}

// returns literal at position i
char RelationMatcher::getIndex(unsigned i) const {
  return indexes_[i];
}

// is a write matcher?
bool RelationMatcher::isWrite() const {
  if((type_ == RelationKind::write) ||
     (type_ == RelationKind::readAndWrite))
    return true;
  else return false;
}

// is a read matcher?
bool RelationMatcher::isRead() const {
  if((type_ == RelationKind::read) ||
     (type_ == RelationKind::readAndWrite))
    return true;
  else return false;
}

// is a readAndWrite matcher?
bool RelationMatcher::isReadAndWrite() const {
  if((type_ == RelationKind::read) ||
     (type_ == RelationKind::write))
    return true;
  else return false;
}

// return matcher type
// 0 for read, 1 for write and 2 readandWrite
int RelationMatcher::getType() const {
  if(type_ == RelationKind::read)
    return 0;
  if(type_ == RelationKind::write)
    return 1;
  else return 2;
}

// return fixed dim at index i
std::vector<isl::pw_aff> RelationMatcher::getDims(int i) const {
  return setDim_[i];
}


// [belong to step 4.(see findAndPrint)]
// TODO: change name and sign of the function as Alex suggested.
// working in progress change soon.
static inline bool isEqual(isl::pw_aff &affOne, isl::pw_aff &affTwo) {
  isl::map mapOne = isl::map::from_pw_aff(affOne);
  isl::map mapTwo = isl::map::from_pw_aff(affTwo);
  isl::pw_multi_aff MultiAffOne = isl::pw_multi_aff::from_map(mapOne);
  isl::pw_multi_aff MultiAffTwo = isl::pw_multi_aff::from_map(mapTwo);

  assert(mapOne.dim(isl::dim::in) == mapTwo.dim(isl::dim::in) &&
        "maps with different input dims");

  assert(mapOne.dim(isl::dim::out) == mapTwo.dim(isl::dim::out) &&
        "maps with different output dims");

  for(size_t i=0; i<mapOne.dim(isl::dim::out); ++i) {
    isl::pw_aff PwAffOne = MultiAffOne.get_pw_aff(i);
    isl::pw_aff PwAffTwo = MultiAffTwo.get_pw_aff(i);
    int indexMapOne = -1;
    int indexMapTwo = -1;
    PwAffOne.foreach_piece([&](isl::set S, isl::aff Aff) -> isl_stat {
      for(size_t j=0; j<mapOne.dim(isl::dim::in); ++j) {
        isl::val V = Aff.get_coefficient_val(isl::dim::in, j);
        if(!V.is_zero())
          indexMapOne = j;
      }
      return isl_stat_ok;
    });
    PwAffTwo.foreach_piece([&](isl::set S, isl::aff Aff) -> isl_stat {
      for(size_t j=0; j<mapTwo.dim(isl::dim::in); ++j) {
        isl::val V = Aff.get_coefficient_val(isl::dim::in, j);
        if(!V.is_zero())
          indexMapTwo = j;
      }
      return isl_stat_ok;
    });
    if(indexMapOne != indexMapTwo)
      return false;
  }
  return true;
}


static bool checkDimensions(isl::pw_aff &pw, std::vector<isl::pw_aff> &dims) {
  bool result = false;
  for(size_t i = 0; i<dims.size(); ++i) {
    if(isEqual(pw,dims[i]))
      result = true;
  }
  return result;
}

// check if the placeholder properties are true for the
// given access.
bool RelationMatcher::checkPlaceHolder(isl::map access) {
  isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
  assert(MultiAff.n_piece() == 1 && "should be single value");
  bool res = true;
  for(unsigned ii=0, ie = access.dim(isl::dim::out); ii != ie; ++ii) {
    isl::pw_aff PwAff = MultiAff.get_pw_aff(ii);
    PwAff.foreach_piece([&](isl::set, isl::aff aff) {
      for(unsigned ji=0, je = access.dim(isl::dim::in); ji != je; ++ji) {
        isl::val v = aff.get_coefficient_val(isl::dim::in, ji);
        if(!v.is_zero()) {
          isl::val coeff = v;
          isl::val inc = aff.get_constant_val();
          //std::cout << "AFF" << aff.to_str() << std::endl;
          //std::cout << "COEFF" << coeff.to_str() << std::endl;
          //std::cout << "INC" << inc.to_str() << std::endl;
          //std::cout << "INDEX" << ii << std::endl;
          //std::cout << "P_C"<< placeHolderSet_[ii].coefficient_.to_str() << std::endl;
          //std::cout << "P_I"<< placeHolderSet_[ii].increment_.to_str() << std::endl;
          if(!placeHolderSet_[ii].coefficient_.eq(coeff) ||
             !placeHolderSet_[ii].increment_.eq(inc)) {
            res = false;
          }
        }
      }
    });
  } 
  return res;
}

// return the accesses matched
// TODO: notice that we modify the accesses. change.
memoryAccess RelationMatcher::getAccess(isl::union_map &accesses) {
 
   memoryAccess res;

   std::vector<isl::map> accessesAsMap;
   accesses.foreach_map([&accessesAsMap](isl::map access) {
     accessesAsMap.push_back(access); });

  for(size_t i=0; i<accessesAsMap.size(); ++i) {
    isl::space Space = accessesAsMap[i].get_space();
    
    if(Space.dim(isl::dim::out) != indexes_.size()) {
      continue;
    }

    isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(accessesAsMap[i]);
    bool equalDims = true;

    for(size_t i=0; i<setDim_.size(); ++i) {
      isl::pw_aff PwAff = MultiAff.get_pw_aff(i);
      bool check = checkDimensions(PwAff, setDim_[i]);
      //std::cout << "[getAccesses] size" << setDim_.size() << std::endl;
      //std::cout << "[getAccesses] PwAff" << PwAff << std::endl;
      //std::cout << "[getAccesses] setDim_[i]" << setDim_[i] << std::endl;
      //std::cout << "[getAccesses CHECK]" << check << std::endl;
      equalDims = equalDims && check;
    }

    if(equalDims) {
      // drop the access that matched.
      // this is done to avoid re-matching the same access.
      accesses = accesses.subtract(isl::union_map(accessesAsMap[i]));
      //std::cout << "AFTER" << accesses << std::endl;
      // we only return the access if it satisfies also the 
      // placeholder properties and not only the index layout.
      if(checkPlaceHolder(accessesAsMap[i])) {
        res.accessMap_ = accessesAsMap[i];
        res.type_ = type_;
        res.valid = true;
        //std::cout << "EQUAL DIMS" << equalDims << std::endl;
      }
    }
  }
  //std::cout << res << std::endl;
  return res;
}

bool ScheduleNodeMatcher::isMatching(const ScheduleNodeMatcher &matcher,
                                     isl::schedule_node node) {
  if (!node.get()) {
    return false;
  }

  if (matcher.current_ == ScheduleNodeType::Any) {
    matcher.capture_ = node;
    return true;
  }

  if (toIslType(matcher.current_) != isl_schedule_node_get_type(node.get())) {
    return false;
  }

  if (matcher.nodeCallback_ && !matcher.nodeCallback_(node)) {
    return false;
  }

  size_t nChildren =
      static_cast<size_t>(isl_schedule_node_n_children(node.get()));
  if (matcher.children_.size() != nChildren) {
    return false;
  }

  for (size_t i = 0; i < nChildren; ++i) {
    if (!isMatching(matcher.children_.at(i), node.child(i))) {
      return false;
    }
  }
  matcher.capture_ = node;
  return true;
}

static bool hasPreviousSiblingImpl(isl::schedule_node node,
                                   const ScheduleNodeMatcher &siblingMatcher) {
  while (isl_schedule_node_has_previous_sibling(node.get()) == isl_bool_true) {
    node = isl::manage(isl_schedule_node_previous_sibling(node.release()));
    if (ScheduleNodeMatcher::isMatching(siblingMatcher, node)) {
      return true;
    }
  }
  return false;
}

static bool hasNextSiblingImpl(isl::schedule_node node,
                               const ScheduleNodeMatcher &siblingMatcher) {
  while (isl_schedule_node_has_next_sibling(node.get()) == isl_bool_true) {
    node = isl::manage(isl_schedule_node_next_sibling(node.release()));
    if (ScheduleNodeMatcher::isMatching(siblingMatcher, node)) {
      return true;
    }
  }
  return false;
}

std::function<bool(isl::schedule_node)>
hasPreviousSibling(const ScheduleNodeMatcher &siblingMatcher) {
  return std::bind(hasPreviousSiblingImpl, std::placeholders::_1,
                   siblingMatcher);
}

std::function<bool(isl::schedule_node)>
hasNextSibling(const ScheduleNodeMatcher &siblingMatcher) {
  return std::bind(hasNextSiblingImpl, std::placeholders::_1, siblingMatcher);
}

std::function<bool(isl::schedule_node)>
hasSibling(const ScheduleNodeMatcher &siblingMatcher) {
  return [siblingMatcher](isl::schedule_node node) {
    return hasPreviousSiblingImpl(node, siblingMatcher) ||
           hasNextSiblingImpl(node, siblingMatcher);
  };
}

std::function<bool(isl::schedule_node)>
hasDescendant(const ScheduleNodeMatcher &descendantMatcher) {
  isl::schedule_node n;
  return [descendantMatcher](isl::schedule_node node) {
    // Cannot use capturing lambdas as C function pointers.
    struct Data {
      bool found;
      const ScheduleNodeMatcher &descendantMatcher;
    };
    Data data{false, descendantMatcher};

    auto r = isl_schedule_node_foreach_descendant_top_down(
        node.get(),
        [](__isl_keep isl_schedule_node *cn, void *user) -> isl_bool {
          auto data = static_cast<Data *>(user);
          if (data->found) {
            return isl_bool_false;
          }

          auto n = isl::manage_copy(cn);
          data->found =
              ScheduleNodeMatcher::isMatching(data->descendantMatcher, n);
          return data->found ? isl_bool_false : isl_bool_true;
        },
        &data);
    return r == isl_stat_ok && data.found;
  };
}

// Are the two matchers equal?
static bool isEqual(RelationMatcher &a, RelationMatcher &b) {
  
  if(a.getIndexesSize() != b.getIndexesSize())
    return false;
   
  bool res = true;
  for(size_t i=0; i<a.getIndexesSize(); ++i) {
    if(a.getIndex(i) != b.getIndex(i)) {
      res = false;
    }
  }
  return res;
}

// remove duplicates from the matchers array.
// This is done since duplicates do not add any additional
// informations.
// For example: read(A,B) , read(A,B) and read(C,B).
// will become read(A,B) and read(C,B).
// Notice that we will take into account later on
// for the two read(A,B) accesses. It does not make
// sense to construct constraint lists with duplicate.
std::vector<RelationMatcher> removeDuplicates(
					std::vector<RelationMatcher> &v) {
  std::vector<RelationMatcher> res = v;
  for(size_t i=0; i<res.size(); ++i) {
    for(size_t j=i+1; j<res.size()-1; ++j) {
      if(isEqual(res[i], res[j])) {
        res.erase(res.begin()+j);
      }
    }
  }
  return res;
} 

// check if an element in the first list is not present
// in the second list. If this is the case we modify the 
// second list adding this element.
void Finder::merge(std::vector<RelationMatcher> &first,
		      std::vector<RelationMatcher> &second) {

  for(size_t i=0; i<second.size(); ++i) {
    bool isPresent = false;
    for(size_t j=0; j<first.size(); ++j) {
      if(isEqual(second[i], first[j]))
        isPresent = true;
    }
    if(!isPresent)
      first.push_back(second[i]);
  } 
}  	

void Finder::findAndPrint() {
  std::vector<memoryAccess> res;
  res = find();
  std::cout << res.size() << std::endl;
  for(size_t i=0; i<res.size(); ++i) {
    std::cout << res[i] << std::endl;
  }
}

std::vector<memoryAccess> Finder::find() {
  
  std::vector<memoryAccess> res;
  
  // the number of read matchers should be 
  // less or equal to the number of reads.
  int size = readMatchers.size();
  if(size > reads.n_map())
    return res;
  
  size = writeMatchers.size();
  if(size > writes.n_map())
    return res;

  size = readAndWriteMatchers.size();
  if(size > reads.n_map() ||
     size > writes.n_map())
    return res;

  std::vector<RelationMatcher> newReadMatchers =
                               removeDuplicates(readMatchers);
  std::vector<RelationMatcher> newWriteMatchers =
                               removeDuplicates(writeMatchers);
  std::vector<RelationMatcher> newReadAndWriteMatchers =
                               removeDuplicates(readAndWriteMatchers);

  //std::cout << newReadMatchers << std::endl;
  //std::cout << newWriteMatchers << std::endl;
  std::vector<RelationMatcher> newMatchersList;
  merge(newMatchersList, newReadMatchers);
  merge(newMatchersList, newReadMatchers);
  merge(newMatchersList, newWriteMatchers);
  merge(newMatchersList, newReadAndWriteMatchers);

  //step 1. Generate constraints for each matcher.
  std::cout << "generating const list\n";
  std::vector<constraints::ConstraintsList> c_lists;
  for(size_t i=0; i<newMatchersList.size(); ++i) {
    c_lists.push_back(constraints::buildMatcherConstraints(newMatchersList[i], 
							  reads, writes));
  }
  
  //std::cout << "constraint lists for matchers" << std::endl;
  std::cout << c_lists << std::endl;
 

  // step 2. find a list that satisfy all the matcher if any.  
  constraints::ConstraintsList c_list;
  for(size_t i=1; i<c_lists.size(); ++i) {
    if(i == 1) {
      c_list = constraints::compareLists(c_lists[0], c_lists[1]);
    }
    else {
      c_list = constraints::compareLists(c_list, c_lists[i]);
    }
  }

  // check empty list.
  if(c_list.dimsInvolved == -1) {
    //std::cout << "empty list\n";
    return res;
  }

  //std::cout << "final constraint list" << std::endl;
  //std::cout << c_list << std::endl;

  // step 3. set the dims for each matcher.
  // TODO: do the same for write and readAndWrite

  for(size_t i=0; i<writeMatchers.size(); ++i) {
    writeMatchers[i].setDims(c_list.constraints);
    writeMatchers[i].set();
  }

  for(size_t i=0; i<readMatchers.size(); ++i) {
    readMatchers[i].setDims(c_list.constraints);
    readMatchers[i].set();
  }

/*
  for(size_t i=0; i<readAndWriteMatchers.size(); ++i) {
    readAndWriteMatchers[i].setDims(c_list.constraints);
    readAndWriteMatchers[i].set();
  }
*/

  // step 4.  store the accesses
  // TODO: do the same for write and readAndWrite
  // getAccess remove the read once matched so
  // we make a copy. (later I will modify it).
  //auto copyReads = reads;
  for(size_t i=0; i<readMatchers.size(); ++i) {
    memoryAccess tmp = readMatchers[i].getAccess(reads);
    if(tmp.valid)
      res.push_back(tmp);
  }
  //std::cout << "writing start\n";
  for(size_t i=0; i<writeMatchers.size(); ++i) {
    memoryAccess tmp = writeMatchers[i].getAccess(writes);
    if(tmp.valid)
      res.push_back(tmp);
  }
/*
  for(size_t i=0; i<readAndWriteMatchers.size(); ++i) {
    //std::cout << "printing read&Write: ";
  }
*/
  //std::cout << "returning" << std::endl;
  return res;
}

// build a new Finder obj.
Finder::Finder(isl::union_map reads,
	       isl::union_map writes,
               std::vector<RelationMatcher> &matchers) {
  this->reads = reads;
  this->writes = writes;
  assert(reads.n_map() != 0 && "empty  reads");
  assert(writes.n_map() != 0 && "empty writes");
  assert(matchers.size() !=0 && "empty matchers");
  for(size_t i=0; i<matchers.size(); ++i) {
    int type = matchers[i].getType();
    // read type.
    if(type == 0) {
      readMatchers.push_back(matchers[i]);
    }
    // write type
    if(type == 1) {
      writeMatchers.push_back(matchers[i]);
    }
    // readAndWrite type
    else if(type == 2) {
      readAndWriteMatchers.push_back(matchers[i]);
    }
  } 
}

int Finder::getSizeReadMatchers() {
  return readMatchers.size();
}

int Finder::getSizeWriteMatchers() {
  return writeMatchers.size();
}

int Finder::getSizeReadAndWriteMatchers() {
  return readAndWriteMatchers.size();
}

} // namespace matchers


namespace constraints {

// check if two single constraint are equal.
bool isEqual(singleConstraint &a, singleConstraint &b) {
  if((std::get<0>(a) == std::get<0>(b)) &&
     (std::get<1>(a).is_equal(std::get<1>(a)))) 
    return true;
  else return false;
}

// remove possible duplicates.
void removeDuplicate(MultipleConstraints &constraints) {
  for(unsigned i=0; i<constraints.size(); ++i) {
    for(unsigned j=i+1; j<constraints.size(); ++j) {
      if(isEqual(constraints[i],constraints[j])) {
        constraints.erase(constraints.begin()+j);
      }
    }
  }
}

// create a new constraints list given two lists.
// we remove duplicates.
void createNewConstraintsList(
		int i,
		int j,
		const ConstraintsList &listOne,
		const ConstraintsList &listTwo,
  		ConstraintsList &res) {
  MultipleConstraints newConstraints;
  
  for(int ii=i; ii<listOne.dimsInvolved+i; ++ii) {
    auto t = std::make_tuple(std::get<0>(listOne.constraints[ii]),
			     std::get<1>(listOne.constraints[ii]));
    newConstraints.push_back(t);
  }

  for(int jj=j; jj<listTwo.dimsInvolved+j; ++jj) {
    auto t = std::make_tuple(std::get<0>(listTwo.constraints[jj]),
			     std::get<1>(listTwo.constraints[jj]));
    newConstraints.push_back(t);
  }

  // remove possible duplicates.
  removeDuplicate(newConstraints);

  res.constraints = newConstraints;
  res.dimsInvolved = newConstraints.size();
}

// are the two vectors equal?
static inline bool isEqualArray(std::vector<int>a, std::vector<int>b) {
  if(a.size() != b.size())
    return false;
  if (std::equal(a.begin(), a.begin() + a.size(), b.begin()))
    return true;
  else return false;
}

// do the isl::pw_aff relate to the same dimensions?. 

static inline bool accessSameDim(isl::pw_aff &affOne, isl::pw_aff &affTwo) {
  isl::map mapOne = isl::map::from_pw_aff(affOne);
  isl::map mapTwo = isl::map::from_pw_aff(affTwo);
  isl::pw_multi_aff MultiAffOne = isl::pw_multi_aff::from_map(mapOne);
  isl::pw_multi_aff MultiAffTwo = isl::pw_multi_aff::from_map(mapTwo);

  assert(mapOne.dim(isl::dim::in) == mapTwo.dim(isl::dim::in) && 
        "maps with different input dims");  

  assert(mapOne.dim(isl::dim::out) == mapTwo.dim(isl::dim::out) &&
	"maps with different output dims");

  for(size_t i=0; i<mapOne.dim(isl::dim::out); ++i) {
    isl::pw_aff PwAffOne = MultiAffOne.get_pw_aff(i);
    isl::pw_aff PwAffTwo = MultiAffTwo.get_pw_aff(i);
    std::vector<int>indexMapOne;
    std::vector<int>indexMapTwo;
    PwAffOne.foreach_piece([&](isl::set S, isl::aff Aff) -> isl_stat {
      for(size_t j=0; j<mapOne.dim(isl::dim::in); ++j) {
        isl::val V = Aff.get_coefficient_val(isl::dim::in, j);
        if(!V.is_zero()) {
          indexMapOne.push_back(j);
        }
      }
      return isl_stat_ok;
    });
    PwAffTwo.foreach_piece([&](isl::set S, isl::aff Aff) -> isl_stat {
      for(size_t j=0; j<mapTwo.dim(isl::dim::in); ++j) {
        isl::val V = Aff.get_coefficient_val(isl::dim::in, j);
        if(!V.is_zero()) {
          indexMapTwo.push_back(j);
        }
      }
      return isl_stat_ok;
    });
    if(!isEqualArray(indexMapOne, indexMapTwo))
      return false;
  }
  return true;
}  
  
// compare two lists and return a new list
// (set of constraints) that satisfies the 
// two input list. It may return an empty list.
// For example:
// 1. (B, i1) and (C, i1) 
// [this should be rejected since i1 is assigned both to B and C]
// 2. (A, i0) and (A, i2) 
// [this should be rejected since A is assigned both to i0 and i2]

ConstraintsList compareLists(
		ConstraintsList &listOne,
  		ConstraintsList &listTwo) {
  ConstraintsList res;
  int sizeListOne = listOne.constraints.size();
  int sizeListTwo = listTwo.constraints.size();
  for(int i=0; i<sizeListOne; i+=listOne.dimsInvolved) {
    for(int j=0; j<sizeListTwo; j+=listTwo.dimsInvolved) {
    bool isPossible = true;
      for(int ii=i; ii<i+listOne.dimsInvolved; ++ii) {
        for(int jj=j; jj<j+listTwo.dimsInvolved; ++jj) {
          //std::cout << "listOne" << std::get<0>(listOne.constraints[ii]) << std::endl;
          //std::cout << "listTwo" << std::get<0>(listTwo.constraints[jj]) << std::endl;
          //std::cout << "listOne" << std::get<1>(listOne.constraints[ii]) << std::endl;
          //std::cout << "listTwo" << std::get<1>(listTwo.constraints[jj]) << std::endl;
          bool condOne = std::get<0>(listOne.constraints[ii]) == std::get<0>(listTwo.constraints[jj]);
          bool condTwo = accessSameDim(std::get<1>(listOne.constraints[ii]), std::get<1>(listTwo.constraints[jj]));
          if((!condOne && condTwo) || (condOne && !condTwo)){
            isPossible = false;
            //std::cout << "not possible\n";
          }
          else {
            //std::cout << "possible\n";
          }
            //std::cout << "###\n";
        }
      }
      //std::cout << "@@@@\n";
      if(isPossible) {
        //std::cout << "OK" <<  std::endl;
        createNewConstraintsList(i,j,listOne,listTwo,res);
      }
    }
  }
  return res;
}

// create the constraints list.
// TODO: add the case for read & write matchers.
ConstraintsList buildMatcherConstraints(
                        matchers::RelationMatcher &matcher,
                        isl::union_map &accessesRead,
			isl::union_map &accessesWrite) {
  ConstraintsList list;
  if(matcher.isRead()) {
    accessesRead.foreach_map([&list, matcher](isl::map access) -> isl_stat {
      isl::space Space = access.get_space();
      if(Space.dim(isl::dim::out) == matcher.getIndexesSize()) {
        assert(access.is_single_valued() && "map is not single value");
        isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
        assert(MultiAff.n_piece() == 1 && "pma not single value");
        for(unsigned u=0; u<access.dim(isl::dim::out); ++u) {
          isl::pw_aff PwAff = MultiAff.get_pw_aff(u);
          auto t = std::make_tuple(matcher.getIndex(u), PwAff);
          list.constraints.push_back(t);
        }
      }
      return isl_stat_ok;
    });
  }
  if(matcher.isWrite()) {
    accessesWrite.foreach_map([&list, matcher](isl::map access) -> isl_stat {
      isl::space Space = access.get_space();
      if(Space.dim(isl::dim::out) == matcher.getIndexesSize()) {
        assert(access.is_single_valued() && "map is not single value");
        isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
        assert(MultiAff.n_piece() == 1 && "pma not single value");
        for(unsigned u=0; u<access.dim(isl::dim::out); ++u) {
          isl::pw_aff PwAff = MultiAff.get_pw_aff(u);
	  auto t = std::make_tuple(matcher.getIndex(u), PwAff);
          list.constraints.push_back(t);
        }
      }
      return isl_stat_ok;
    });
  }
  list.dimsInvolved = matcher.getIndexesSize();
  return list;
}

} // namespace constraints

