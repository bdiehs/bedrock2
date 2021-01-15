
#include <stdio.h>
#include <stdint.h>

void createTimestampMsgResponse(uint8_t *buffer);
int64_t getIntFromMessage(char* message);
void createMessage(char* buffer, int64_t x);
void print_msg(const char* cstr, int length);
