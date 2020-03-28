#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include "message.h"


// int64_t increment(int64_t x) {
// 	return x+1;
// }

int main(int argc, char *argv[]) {
	// port to start the server on
	int SERVER_PORT = 8877;

	// socket address used for the server
	struct sockaddr_in server_address;
	memset(&server_address, 0, sizeof(server_address));
	server_address.sin_family = AF_INET;

	// htons: host to network short: transforms a value in host byte
	// ordering format to a short value in network byte ordering format
	server_address.sin_port = htons(SERVER_PORT);

	// htons: host to network long: same as htons but to long
	server_address.sin_addr.s_addr = htonl(INADDR_ANY);

	// create a UDP socket, creation returns -1 on failure
	int sock;
	if ((sock = socket(PF_INET, SOCK_DGRAM, 0)) < 0) {
		printf("could not create socket\n");
		return 1;
	}

	// bind it to listen to the incoming connections on the created server
	// address, will return -1 on error
	if ((bind(sock, (struct sockaddr *)&server_address,
	          sizeof(server_address))) < 0) {
		printf("could not bind socket\n");
		return 1;
	}

	// socket address used to store client address
	struct sockaddr_in client_address;
	int client_address_len = sizeof(client_address);

	// run indefinitely
	while (true) {
		char buffer[1024];
		// read content into buffer from an incoming client
		int len = recvfrom(sock, buffer, sizeof(buffer), 0,
		                   (struct sockaddr *)&client_address,
		                   &client_address_len);

		// inet_ntoa prints user friendly representation of the
		// ip address

		buffer[len] = '\0';
		printf("received from client %s:\n",
		       inet_ntoa(client_address.sin_addr));
		print_msg(buffer, 1024);

		// int64_t x = getIntFromMessage(buffer);
		char buffer_out[1024];
		createTimestampMsgResponse(buffer_out);
		printf("sending:\n");
		print_msg(buffer_out, 360);
		// createMessage(buffer_out, increment(x));
		// send same content back to the client ("echo")
		sendto(sock, buffer_out, 360, 0, (struct sockaddr *)&client_address,
		       client_address_len);
	}

	return 0;
}
//TODO:
//Parse and print request by google client
//Print and send a response in the google roughtime format
// send MIDP and RADI and 42 for all other fields
