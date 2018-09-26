#include <iostream>
using std::cout;
using std::endl;
#include <vector>
using std::vector;
#include <utility> //pair
using std::pair;
using std::swap;
#include <algorithm>
using std::sort;

class Pair : public pair<char,char> {
};
bool operator<(const Pair & l, const Pair & r){
	return l.first<r.first;
}

class CP : public vector<Pair> {
public:
	void normalize(){
		for(auto p=this->begin(); p!= this->end(); p++)
			if(p->first>p->second)
				std::swap(p->first,p->second);
		std::sort(this->begin(),this->end());
	}
};

class CPT : public CP {
public:
	char t[3];
};

int main(int argc, char * argv[]){
	cout<<"Hello!"<<endl;
}
