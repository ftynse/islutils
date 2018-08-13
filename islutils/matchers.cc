#include "islutils/matchers.h"
#include <iostream>
using namespace std;

namespace matchers {

void RelationMatcher::setDims(constraints::MultipleConstraints &mc) {
  std::vector<isl::pw_aff> tmp;
  for(std::size_t i=0; i<indexes_.size(); ++i) {
    for(std::size_t j=0; j<mc.size(); ++j) {
      if(indexes_[i] == std::get<0>(mc[j])) {
        tmp.push_back(std::get<1>(mc[j]));
      }
    }
    //std::cout << tmp << std::endl;
    setDim_.push_back(tmp);
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

// check if the dimension statisfies the matcer.
static bool checkDimension(isl::pw_aff &pw, std::vector<isl::pw_aff> &dims) {
  bool result = false;
  for(size_t i = 0; i<dims.size(); ++i) {
    std::cout << "matcher: " << dims[i] << std::endl;
    std::cout << "pw :" << pw << std::endl;
    if(dims[i].is_equal(pw))
      result = true;
  }
  return result;
}
// return the accesses matched
std::vector<isl::map> RelationMatcher::getAccesses(isl::union_map &accesses) {
  std::vector<isl::map> res;
  std::cout << accesses << std::endl;
  accesses.foreach_map([&](isl::map access) -> isl_stat {
    isl::space Space = access.get_space();
    
    if(Space.dim(isl::dim::out) != indexes_.size()) {
      std::cout << "returning" << std::endl;
      return isl_stat_ok;
    }

    isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
    bool equalDims = true;

    for(size_t i=0; i<setDim_.size(); ++i) {
      //std::cout << "Size" << setDim_.size() << std::endl;
      isl::pw_aff PwAff = MultiAff.get_pw_aff(i);
      //std::cout << "setDim" << setDim_[i] << std::endl;
      bool check = checkDimension(PwAff, setDim_[i]);
      equalDims = equalDims && check;
    }

    //std::cout << equalDims << std::endl;
    if(equalDims) {
      res.push_back(access);
      // drop the access that matched.
      //isl::map alreadyMatched = accesses.extract_map(access.get_space());
      //accesses = accesses.subtract(isl::union_map(access));
    }
    
    return isl_stat_ok;
    
  });
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

// Finder methods.
// The "Finder" class takes as input the Scop and a collection
// of matchers. It return the accesses that match
// for any partial schedule detected into the Scop.


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

// remove dumplicates from the matchers array.
// This is done since duplicates do not add any additional
// informations.
// For example: read(A,B) , read(A,B) and read(C,B).
// will become read(A,B) and read(C,B).
// Notice that we will take into account later on
// for the two read(A,B) accesses. It does not make
// sense to construct constrainst lists for duplicate.
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

// find
void Finder::findAndPrint() {

  int size = readMatchers.size();
  if(size > reads.n_map()) 
    return;
 
  size = writeMatchers.size();  
  if(size > writes.n_map())
    return;
  
  size = readAndWriteMatchers.size(); 
  if(size > reads.n_map() ||
     size > writes.n_map())
    return;

  std::vector<RelationMatcher> newReadMatchers = 
  			       removeDuplicates(readMatchers);
  std::vector<RelationMatcher> newWriteMatchers = 
                               removeDuplicates(writeMatchers);
  std::vector<RelationMatcher> newReadAndWriteMatchers = 
                               removeDuplicates(readAndWriteMatchers);

  //std::cout << newReadMatchers << std::endl;
  //std::cout << newWriteMatchers << std::endl;
  //std::cout << newReadAndWriteMatchers << std::endl;
  merge(newReadMatchers, newWriteMatchers);
  merge(newReadMatchers, newReadAndWriteMatchers);
  //std::cout << newReadMatchers << std::endl;
  //std::cout << "writes : " << writes << std::endl;

  // step 1. Generate constraints for each matcher.
  std::vector<constraints::ConstraintsList> c_lists;
  for(size_t i=0; i<newReadMatchers.size(); ++i) {
    c_lists.push_back(constraints::buildMatcherConstraints(newReadMatchers[i], 
							  reads));
  }
  std::cout << c_lists << std::endl;

  // step 2. find a list that satisfy all the matcher if any.  
  constraints::ConstraintsList c_list; 
  for(size_t i=0; i<c_lists.size(); ++i) {
    if(i <= 1) {
      c_list = constraints::compareLists(c_lists[0], c_lists[1]);
    }
    else {
      c_list = constraints::compareLists(c_list, c_lists[i]);
    }
  }

  // step 3. set the dims for each matcher.
  // TODO: do the same for write and readAndWrite
/*
  for(size_t i=0; i<readMatchers.size(); ++i) {
    readMatchers[i].setDims(c_list.constraints);
    readMatchers[i].set();
  }
*/
  for(size_t i=0; i<writeMatchers.size(); ++i) {
    writeMatchers[i].setDims(c_list.constraints);
    writeMatchers[i].set();
  }
/*
  for(size_t i=0; i<readAndWriteMatchers.size(); ++i) {
    readAndWriteMatchers[i].setDims(c_list.constraints);
    readAndWriteMatchers[i].set();
  }
*/

  // step 4. print the accesses matched.
  // TODO: do the same for write and readAndWrite
  for(size_t i=0; i<readMatchers.size(); ++i) {
    //std::cout << "printing read: ";
    //std::cout << readMatchers[i].getAccesses(reads) << std::endl;
  }
  for(size_t i=0; i<writeMatchers.size(); ++i) {
    std::cout << "printing write: ";
    std::cout << writeMatchers[i].getAccesses(writes) << std::endl;
  }
  for(size_t i=0; i<readAndWriteMatchers.size(); ++i) {
    std::cout << "printing read&Write: ";
  }

  return;
}


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

// remove possible dumpicates
void removeDuplicate(MultipleConstraints &constraints) {
  for(unsigned i=0; i<constraints.size(); ++i) {
    for(unsigned j=i+1; j<constraints.size(); ++j) {
      if(isEqual(constraints[i],constraints[j])) {
        constraints.erase(constraints.begin()+j);
      }
    }
  }
}

// create a new constraints list.
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

// given two constraints lists compare them and
// return a new constraint list. 
// for now we just compare all the possible tuples
// and check if they do not conflict.
// For example:
// 1. (B, i1) and (C, i1) [this should be rejected since i1 is assigned both to B and C]
// 2. (A, i0) and (A, i2) [this should be rejected since A is assigned both to i0 and i2]
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
          if((std::get<0>(listOne.constraints[ii]) != std::get<0>(listTwo.constraints[jj]) &&
             (std::get<1>(listOne.constraints[ii]).is_equal(std::get<1>(listTwo.constraints[jj])) == 1)) ||
             (std::get<0>(listOne.constraints[ii]) == std::get<0>(listTwo.constraints[jj]) &&
 	     (std::get<1>(listOne.constraints[ii]).is_equal(std::get<1>(listTwo.constraints[jj])) == 0))) {
            isPossible = false;
          }
          else {
          }
        }
      }
      if(isPossible) {
        createNewConstraintsList(i,j,listOne,listTwo,res);
      }
    }
  }
  return res;
}

// create the constraints list.
ConstraintsList buildMatcherConstraints(
                        matchers::RelationMatcher &matcher,
                        isl::union_map &accesses) {
  ConstraintsList list;
  accesses.foreach_map([&list, matcher](isl::map access) -> isl_stat {
    isl::space Space = access.get_space();
    if(Space.dim(isl::dim::out) == matcher.getIndexesSize()) {
      isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
      for(unsigned u=0; u<access.dim(isl::dim::out); ++u) {
        isl::pw_aff PwAff = MultiAff.get_pw_aff(u);
        //std::cout << "PwAff" << PwAff << std::endl;
        //std::cout << "Space PwAff" << PwAff.get_space() << std::endl;
        //std::cout << "Domain Space" << PwAff.get_domain_space() << std::endl;
        //std::cout << "project OUT" << PwAff.project_domain_on_params() << std::endl;
        //std::cout << "domain Set:" << PwAff.domain().to_str() << std::endl;
        //std::cout << "param set: " << PwAff.params().to_str() << std::endl;
        // new part
        PwAff.foreach_piece([&](isl::set S, isl::aff Aff) -> isl_stat {
          for(unsigned uu=0; uu<access.dim(isl::dim::in); ++uu) {
   	    isl::val V = Aff.get_coefficient_val(isl::dim::in, uu);
            std::cout << V.to_str() << std::endl;
            if (!V.is_zero()) {
              std::cout << "LoopDim" << uu << std::endl;
            }
          }
          return isl_stat_ok;
        });
        // end new part. 
        auto t = std::make_tuple(matcher.getIndex(u), PwAff);
        list.constraints.push_back(t);
      }
    }
    return isl_stat_ok;
  });
  list.dimsInvolved = matcher.getIndexesSize();
  return list;
}


/*
// create the constraints list for reads.
ConstraintsList buildMatcherConstraintsReads(
			matchers::RelationMatcher &matcher,
			isl::union_map &accessesReads) {
  ConstraintsList list;
  accessesReads.foreach_map([&list, matcher](isl::map access) -> isl_stat {
    isl::space Space = access.get_space();
    if(Space.dim(isl::dim::out) == matcher.getIndexesSize()) {
      isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
      for(unsigned u=0; u<access.dim(isl::dim::out); ++u) {
        isl::pw_aff PwAff = MultiAff.get_pw_aff(u);
        auto t = std::make_tuple(matcher.getIndex(u), PwAff);
	list.constraints.push_back(t);
      }
    }
    return isl_stat_ok;
  });
  list.dimsInvolved = matcher.getIndexesSize();
  return list;
}
*/
/*
// create the constraints for writes.
ConstraintsList buildMatcherConstraintsWrites(
			matchers::RelationMatcher &matcher,
			isl::union_map &accessesWrites) {
  ConstraintsList list;
  accessesWrites.foreach_map([&list, matcher](isl::map access) -> isl_stat {
    isl::space Space = access.get_space();
    if(Space.dim(isl::dim::out) == matcher.getIndexesSize()) {
      isl::pw_multi_aff MultiAff = isl::pw_multi_aff::from_map(access);
      for(unsigned u=0; u<access.dim(isl::dim::out); ++u) {
        isl::pw_aff PwAff = MultiAff.get_pw_aff(u);
        auto t = std::make_tuple(matcher.getIndex(u), PwAff);
        list.constraints.push_back(t);
      }
    }
    return isl_stat_ok;
  });
  list.dimsInvolved = matcher.getIndexesSize();
  return list;
}
*/
 
} // namespace constraints

