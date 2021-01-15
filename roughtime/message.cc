#include "message.h"
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <time.h>

int64_t getIntFromMessage(char* message) {
  int64_t n = 0;
  memcpy(&n, message + 88, 8);
  	return n;
}

void addToBuffer(uint8_t* buffer, int64_t x, int start, int num_bytes) {
  for (int i=0; i<num_bytes; i++) {
    buffer[start+i] = (x >> 8*i) & 0xFF;
  }
}

// void createMessage(char* buffer, int64_t x) {
//   addToBuffer(buffer, 3, 0, 4);
//   addToBuffer(buffer, 0x40, 4, 4);
//   addToBuffer(buffer, 0x48, 8, 4);

//   memcpy(buffer + 12, "NONC", 4);
//   memcpy(buffer + 16, "INTN", 4);
//   memcpy(buffer + 20, "PAD\xff", 4);
//   for (int i=0; i<64; i++) {
//     buffer[24 + i] = 0;
//   }
//   memcpy(buffer + 88, (char *)&x, 8);
//   for (int i=96; i<1024; i++) {
//     buffer[i] = 0;
//   }
// }

void createTimestampMsgResponse(uint8_t *buffer) {

  addToBuffer(buffer, 5, 0, 4);
  addToBuffer(buffer, 0x40, 4, 4);
  addToBuffer(buffer, 0x40, 8, 4);
  addToBuffer(buffer, 0xa4, 12, 4);
  addToBuffer(buffer, 0x13c, 16, 4);

  memcpy(buffer + 20, "SIG", 3);
  buffer[23] = 0;
  memcpy(buffer + 24, "PATH", 4);
  memcpy(buffer + 28, "SREP", 4);
  memcpy(buffer + 32, "CERT", 4);
  memcpy(buffer + 36, "INDX", 4);
  for (int i=0; i<64; i++) {
  	buffer[40 + i] = 0x42;
  }

  addToBuffer(buffer, 3, 104, 4);
  addToBuffer(buffer, 4, 108, 4);
  addToBuffer(buffer, 0xc, 112, 4);

  memcpy(buffer + 116, "RADI", 4);
  memcpy(buffer + 120, "MIDP", 4);
  memcpy(buffer + 124, "ROOT", 4);

  addToBuffer(buffer, 1000000, 128, 4);
  int64_t timestamp = 1000000 * time(NULL);
  addToBuffer(buffer, timestamp, 132, 8);

  for (int i=0; i<64; i++) {
  	buffer[140+i] = 0x42;
  }
  addToBuffer(buffer, 2, 204, 4);
  addToBuffer(buffer, 0x40, 208, 4);

  memcpy(buffer + 212, "SIG", 3);
  buffer[215] = 0;
  memcpy(buffer + 216, "DELE", 4);
  for (int i=0; i<64; i++) {
  	buffer[220+i] = 0x42;
  }
  addToBuffer(buffer, 3, 284, 4);
  addToBuffer(buffer, 0x20, 288, 4);
  addToBuffer(buffer, 0x28, 292, 4);

  memcpy(buffer + 296, "PUBK", 4);
  memcpy(buffer + 300, "MINT", 4);
  memcpy(buffer + 304, "MAXT", 4);

  for (int i=0; i<48; i++) {
  	buffer[308+i] = 0x42;
  }
  for (int i=0; i<4; i++) {
  	buffer[356+i] = 0x43;
  }
  // for (int i=360; i<1024; i++) {
  // 	buffer[i] = 0x42;
  // }
}

void print_msg(const char* cstr, int length) {
  if (length%4 != 0) {
    printf("Length must be multiple of 4");
    exit(1);
  }
  for (int i=0; i<length; i+=4) {
    for (int j=0; j<4; j++) {
      printf("%02hhx", cstr[i+j]);
    }
    printf("\t");
    for (int j=0; j<4; j++) {
      if (!isprint(cstr[i+j])) {
        printf(".");
      } else {
        printf("%c", cstr[i+j]);
      }

    }
    printf("\n");
    
  }
}
