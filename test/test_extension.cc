#include "islutils/device_extension/device_transform.h"
#include <iostream>
int main(int argc, char **argv) {
  bool computeSchedule = true;
  if (argc > 2 && !argv[2]) {
    computeSchedule = false;
  }
  runAllFlow(argv[1], computeSchedule);
}


