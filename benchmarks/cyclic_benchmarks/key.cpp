#include <sstream>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string.h>
#include <string>
#include <set>
#include <stdio.h>
#include <cstdio>
#include <vector>
#include <math.h>
#include <stdlib.h>
#include <iterator>
#include <assert.h>
#include <map>
#include <stdbool.h>
//#include <stdiio.h>

using namespace std;

int main(int argc, char ** argv){

	std::string line="";
	std::ifstream  infile(argv[1]);
	std::ifstream  infile2(argv[2]);
	//std::ofstream  outfile(argv[2]);
	

	//int length_of_path = atoi(argv[2]);
	//int num_of_iterations = atoi(argv[3]);

	string  temp, temp1, temp2, temp5;
	int infile_line_count=0;

	while(!infile.eof())
	{	
		std::getline(infile,line);

		if(line == "")
			continue;
		stringstream ss(line);
		ss >> temp5; 
		
		if(temp5 == "#")
		{
			ss >> temp5;
			std::size_t found = temp5.find("=");
			if(found != std::string::npos)
				break;
		}

		temp5 = "key=";
		break;	
	}//////finish first iteration of file reading

	//cout << "hehe" << endl;

	int tran_key_bits = temp5.length() - 4;


	int num_of_key_bits = 0;
	while(!infile2.eof())
	{
		std::getline(infile2,line);

		if(line == "")
			continue;
		stringstream ss(line);
		ss >> temp; 


		std::size_t found100 = line.find("#");
		if(found100 != std::string::npos)
			continue;
	
		std::size_t found0=temp.find_first_of("(");
		temp2=temp.substr(0,found0);
		if (temp2=="INPUT")
		{
			std::size_t found=temp.find_first_of("(");
			std::size_t found2=temp.find_first_of(")");
			temp1= temp.substr(found+1,found2-found-1);
		
			std::size_t found7 = temp1.find_first_of("t");
			string temp3 = temp1.substr(0, found7+1);
			if(temp3 == "keyinput")
			{
				//temp3 = temp1.substr(found7+1, temp1.size()-8);
				//int key_bit = atoi(temp3.c_str());
				//if(key_bit > max_key)
				//	max_key = key_bit;
				num_of_key_bits++ ;
			}		
			continue;
		}
	}
	
	assert (num_of_key_bits > tran_key_bits);

	while( tran_key_bits < num_of_key_bits)
	{
		temp5 = temp5 + "1";
		tran_key_bits++;
	}

	cout <<  temp5;	

	return 0;
}

