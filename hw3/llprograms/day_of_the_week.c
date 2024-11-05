#include <stdint.h>

struct div_t {
  int64_t quot;
  int64_t rem;
};

void div(struct div_t* result, int64_t numer, int64_t denom) {
  int64_t quot = 0;
  int64_t rem = numer;
  while (rem >= denom) {
    rem -= denom;
    quot++;
  }
  result->quot = quot;
  result->rem = rem;
}

static const char* magic = "-bed=pen+mad.";

int64_t day_of_the_week(int64_t y, int64_t m, int64_t d) {
  int64_t result = 0;
  struct div_t div_result;

  y -= m < 3;

  result = y;

  div(&div_result, y, 4);
  result += div_result.quot;

  div(&div_result, y, 100);
  result -= div_result.quot;

  div(&div_result, y, 400);
  result += div_result.quot;

  result += magic[m];

  result += d;

  div(&div_result, result, 7);
  return div_result.rem;
}
