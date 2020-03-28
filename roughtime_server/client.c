#include <arpa/inet.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#include "message.h"




int main() {
	const char* server_name = "localhost";
	const int server_port = 8877;

	struct sockaddr_in server_address;
	memset(&server_address, 0, sizeof(server_address));
	server_address.sin_family = AF_INET;

	// creates binary representation of server name
	// and stores it as sin_addr
	// http://beej.us/guide/bgnet/output/html/multipage/inet_ntopman.html
	inet_pton(AF_INET, server_name, &server_address.sin_addr);

	// htons: port in network order format
	server_address.sin_port = htons(server_port);

	// open socket
	int sock;
	if ((sock = socket(PF_INET, SOCK_DGRAM, 0)) < 0) {
		printf("could not create socket\n");
		return 1;
	}

	// data that will be sent to the server

	char data_to_send[1024];
	printf("Enter a number:\n");
	int64_t x;
	scanf("%lld", &x);
	createMessage(data_to_send, x);
	printf("sent: \n");
	print_msg(data_to_send, 360);

	// send data
	int len =
	    sendto(sock, data_to_send, sizeof(data_to_send), 0,
	           (struct sockaddr*)&server_address, sizeof(server_address));
		// received echoed data back
	char buffer[1024];
	// fprintf(stderr, "before recv\n");
	// printf("buff_size: %d\n", len);
	int server_addr_len = sizeof(server_address);
	int resp = recvfrom(sock, buffer, sizeof(buffer), 0, (struct sockaddr*)&server_address, &server_addr_len);
	if (resp == -1) {
		printf("Error\n");
		close(sock);
		return 1;
	}
	// fprintf(stderr, "after recv\n");


	buffer[len] = '\0';
	printf("received: \n");
	print_msg(buffer, 360);
	printf("final output from server %lld\n", getIntFromMessage(buffer));
	// close the socket
	close(sock);
	return 0;
}