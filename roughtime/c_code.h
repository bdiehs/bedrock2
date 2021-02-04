#include <stdint.h>
#include <memory.h>

// LITTLE-ENDIAN memory access is REQUIRED
// the following two functions are required to work around -fstrict-aliasing
static inline uintptr_t _br2_load(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sz);
  return r;
}

static inline void _br2_store(uintptr_t a, uintptr_t v, size_t sz) {
  memcpy((void*)a, &v, sz);
}


void createTimestampMessage(uintptr_t buffer) {
  uintptr_t i;
  _br2_store(buffer, (uintptr_t)5ULL, 4);
  _br2_store((buffer)+((uintptr_t)4ULL), (uintptr_t)64ULL, 4);
  _br2_store((buffer)+((uintptr_t)8ULL), (uintptr_t)64ULL, 4);
  _br2_store((buffer)+((uintptr_t)12ULL), (uintptr_t)164ULL, 4);
  _br2_store((buffer)+((uintptr_t)16ULL), (uintptr_t)316ULL, 4);
  _br2_store((buffer)+((uintptr_t)20ULL), (uintptr_t)4671827ULL, 4);
  _br2_store((buffer)+((uintptr_t)24ULL), (uintptr_t)1213481296ULL, 4);
  _br2_store((buffer)+((uintptr_t)28ULL), (uintptr_t)1346720339ULL, 4);
  _br2_store((buffer)+((uintptr_t)32ULL), (uintptr_t)1414677827ULL, 4);
  _br2_store((buffer)+((uintptr_t)36ULL), (uintptr_t)1480871497ULL, 4);
  i = (uintptr_t)64ULL;
  while (i) {
    i = (i)-((uintptr_t)4ULL);
    _br2_store(((buffer)+((uintptr_t)100ULL))-(i), (uintptr_t)66ULL, 4);
  }
  _br2_store((buffer)+((uintptr_t)104ULL), (uintptr_t)3ULL, 4);
  _br2_store((buffer)+((uintptr_t)108ULL), (uintptr_t)4ULL, 4);
  _br2_store((buffer)+((uintptr_t)112ULL), (uintptr_t)12ULL, 4);
  _br2_store((buffer)+((uintptr_t)116ULL), (uintptr_t)1229209938ULL, 4);
  _br2_store((buffer)+((uintptr_t)120ULL), (uintptr_t)1346652493ULL, 4);
  _br2_store((buffer)+((uintptr_t)124ULL), (uintptr_t)1414483794ULL, 4);
  _br2_store((buffer)+((uintptr_t)128ULL), (uintptr_t)16962ULL, 4);
  _br2_store((buffer)+((uintptr_t)132ULL), (uintptr_t)1111638594ULL, 4);
  i = (uintptr_t)64ULL;
  while (i) {
    i = (i)-((uintptr_t)4ULL);
    _br2_store(((buffer)+((uintptr_t)200ULL))-(i), (uintptr_t)66ULL, 4);
  }
  _br2_store((buffer)+((uintptr_t)204ULL), (uintptr_t)2ULL, 4);
  _br2_store((buffer)+((uintptr_t)208ULL), (uintptr_t)64ULL, 4);
  _br2_store((buffer)+((uintptr_t)212ULL), (uintptr_t)4671827ULL, 4);
  _br2_store((buffer)+((uintptr_t)216ULL), (uintptr_t)1162626372ULL, 4);
  i = (uintptr_t)64ULL;
  while (i) {
    i = (i)-((uintptr_t)4ULL);
    _br2_store(((buffer)+((uintptr_t)280ULL))-(i), (uintptr_t)66ULL, 4);
  }
  _br2_store((buffer)+((uintptr_t)284ULL), (uintptr_t)3ULL, 4);
  _br2_store((buffer)+((uintptr_t)288ULL), (uintptr_t)32ULL, 4);
  _br2_store((buffer)+((uintptr_t)292ULL), (uintptr_t)40ULL, 4);
  _br2_store((buffer)+((uintptr_t)296ULL), (uintptr_t)1262638416ULL, 4);
  _br2_store((buffer)+((uintptr_t)300ULL), (uintptr_t)1414416717ULL, 4);
  _br2_store((buffer)+((uintptr_t)304ULL), (uintptr_t)1415070029ULL, 4);
  i = (uintptr_t)48ULL;
  while (i) {
    i = (i)-((uintptr_t)4ULL);
    _br2_store(((buffer)+((uintptr_t)352ULL))-(i), (uintptr_t)66ULL, 4);
  }
  _br2_store((buffer)+((uintptr_t)356ULL), (uintptr_t)67ULL, 4);
  return;
}

