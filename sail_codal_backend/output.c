#include "sail.h"
#include "sail_config.h"
#include "rts.h"
#include "elf.h"
#ifdef __cplusplus
extern "C" {
#endif
void (*sail_rts_set_coverage_file)(const char *) = NULL;

// union exception
enum kind_zexception { Kind_z__dummy_exnz3 };

struct zexception {
  enum kind_zexception kind;
  union {struct { unit z__dummy_exnz3; };} variants;
};

static void CREATE(zexception)(struct zexception *op) {
  op->kind = Kind_z__dummy_exnz3;
}

static void RECREATE(zexception)(struct zexception *op) {

}

static void KILL(zexception)(struct zexception *op) {
  {}
}

static void COPY(zexception)(struct zexception *rop, struct zexception op) {
  {};
  rop->kind = op.kind;
  if (op.kind == Kind_z__dummy_exnz3) {
    rop->variants.z__dummy_exnz3 = op.variants.z__dummy_exnz3;
  }
}

static bool EQUAL(zexception)(struct zexception op1, struct zexception op2) {
  if (op1.kind == Kind_z__dummy_exnz3 && op2.kind == Kind_z__dummy_exnz3) {
    return EQUAL(unit)(op1.variants.z__dummy_exnz3, op2.variants.z__dummy_exnz3);
  } else return false;
}

static void z__dummy_exnz3(struct zexception *rop, unit op) {
  {}
  rop->kind = Kind_z__dummy_exnz3;
  rop->variants.z__dummy_exnz3 = op;
}

struct zexception *current_exception = NULL;

bool have_exception = false;

sail_string *throw_location = NULL;

unit zinitializze_registers(unit);

unit zinitializze_registers(unit z3zE0)
{
  __label__ end_function_1, end_block_exception_2;

  unit z8zE0;
  z8zE0 = UNIT;
end_function_1: ;
  return z8zE0;
end_block_exception_2: ;

  return UNIT;
}



void model_init(void)
{
  setup_rts();
  current_exception = sail_new(struct zexception);
  CREATE(zexception)(current_exception);
  throw_location = sail_new(sail_string);
  CREATE(sail_string)(throw_location);
}

void model_fini(void)
{
  cleanup_rts();
  if (have_exception) {fprintf(stderr, "Exiting due to uncaught exception: %s\n", *throw_location);}
  KILL(zexception)(current_exception);
  sail_free(current_exception);
  KILL(sail_string)(throw_location);
  sail_free(throw_location);
  if (have_exception) {exit(EXIT_FAILURE);}
}

void model_pre_exit()
{
}

int model_main(int argc, char *argv[])
{
  model_init();
  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);
  zmain(UNIT);
  model_fini();
  model_pre_exit();
  return EXIT_SUCCESS;
}

const size_t SAIL_TEST_COUNT = 0;
unit (*const SAIL_TESTS[1])(unit) = {
  NULL
};
const char* const SAIL_TEST_NAMES[1] = {
  NULL
};

void model_test(void)
{
  for (size_t i = 0; i < SAIL_TEST_COUNT; ++i) {
    model_init();
    printf("Testing %s\n", SAIL_TEST_NAMES[i]);
    SAIL_TESTS[i](UNIT);
    printf("Pass\n");
    model_fini();
  }
}

int main(int argc, char *argv[])
{
  int retcode;
  retcode = model_main(argc, argv);
  return retcode;
}

#ifdef __cplusplus
}
#endif
