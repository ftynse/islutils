#ifndef TEST_EXTENSION_H
#define TEST_EXTENSION_H
#include <islutils/scop.h>
#include "pet.h"

class TestContext {
public:
  Scop* s_;
  pet_scop* petScop_;
  std::string fileName_;
  isl_ctx* ctx_;

  TestContext(Scop* s, pet_scop* petScop, std::string fileName, isl_ctx* ctx)
  :s_(s), petScop_(petScop), fileName_(fileName), ctx_(ctx) 
  {
  }
};
#endif TEST_EXTENSION_H
