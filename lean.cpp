#include<bits/stdc++.h> 
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;
template<class T> using ordered_set =tree<T, null_type, less<T>, rb_tree_tag,tree_order_statistics_node_update> ;
typedef tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update> pbds;
using namespace  std;
#define ll long long int 
#define PIE 3.14159265358979323846264338327
#define all(x) (x).begin(), (x).end() //    sort(all(v));
#define rall(x) (x).rbegin(),(x).rend() // sort(rall(v));
#define nl "\n"
#define MOD 1000000007
#define alice cout<<"ALICE"<<endl
unsigned long long bigNumber = 1000000000000000000ULL;
#define bob cout<<"BOB"<<endl
#define pn cout<<"NO"<<endl
#define py cout<<"YES"<<endl
#define pminus cout<<-1<<endl
#define spc " "
#define pans cout<<"ans = "
#define pzero cout<<0<<endl
#define give(x) cout << x << endl
#define nline cout<<"\n"
#define print(v) for(int i=0; i<v.size(); i++)cout<<v[i]<<" ";cout<<endl;
#define read(v,n) for(int i=0;i<n;i++)cin>>v[i];
#define vi vector<long long int>
using pi = pair<ll,ll>;

int dx[] = {0, 0, 1, -1, 1, 1, -1, -1};
int dy[] = {1, -1, 0, 0, 1, -1, 1, -1};
class DisjointSet {
    vector<int> rank, parent, size; 
public: 
    DisjointSet(int n) {
        rank.resize(n+1, 0); 
        parent.resize(n+1);
        size.resize(n+1); 
        for(int i = 0;i<=n;i++) {
            parent[i] = i; 
            size[i] = 1; 
        }
    }

    int findUPar(int node) {
        if(node == parent[node])
            return node; 
        return parent[node] = findUPar(parent[node]); 
    }

    void unionByRank(int u, int v) {
        int ulp_u = findUPar(u); 
        int ulp_v = findUPar(v); 
        if(ulp_u == ulp_v) return; 
        if(rank[ulp_u] < rank[ulp_v]) {
            parent[ulp_u] = ulp_v; 
        }
        else if(rank[ulp_v] < rank[ulp_u]) {
            parent[ulp_v] = ulp_u; 
        }
        else {
            parent[ulp_v] = ulp_u; 
            rank[ulp_u]++; 
        }
    }

    void unionBySize(int u, int v) {
        int ulp_u = findUPar(u); 
        int ulp_v = findUPar(v); 
        if(ulp_u == ulp_v) return; 
        if(size[ulp_u] < size[ulp_v]) {
            parent[ulp_u] = ulp_v; 
            size[ulp_v] += size[ulp_u]; 
        }
        else {
            parent[ulp_v] = ulp_u;
            size[ulp_u] += size[ulp_v]; 
        }
    }
}; 

ll seg[4*200005];
vector<ll>segvector(2e5+5);
ll lazy[4 *200005 ];
void buildTREEMAX(ll ind , ll low , ll high ){
    if(low==high){
        seg[ind] = segvector[low]; return;
    }
    ll mid = (low+high)/2;
    buildTREEMAX(2*ind +1 , low , mid);
    buildTREEMAX(2*ind+2, mid+1,high);
    seg[ind] = max(seg[2*ind +1], seg[2*ind+2]);
}

void buildTREEMIN(ll ind , ll low , ll high ){
    if(low==high){
        seg[ind] = segvector[low]; return;
    }
    ll mid = (low+high)/2;
    buildTREEMIN(2*ind +1 , low , mid);
    buildTREEMIN(2*ind+2, mid+1,high);
    seg[ind] = min(seg[2*ind +1], seg[2*ind+2]);
}

void updateMIN(ll ind , ll low , ll high , ll position , ll val){
if(low==high ) { seg[ind] = val ; return ;}
ll mid = (low+high) >>1 ;
if(position<= mid ) updateMIN(2*ind+1 , low , mid , position , val);
else updateMIN(2*ind+2 , mid+1 , high , position , val);
seg[ind] = min(seg[2*ind +1], seg[2*ind+2]);}

void updateMAX(ll ind , ll low , ll high , ll position , ll val){
if(low==high ) { seg[ind] = val ; return ;}
ll mid = (low+high) >>1 ;
if(position<= mid ) updateMAX(2*ind+1 , low , mid , position , val);
else updateMAX(2*ind+2 , mid+1 , high , position , val);
seg[ind] = max(seg[2*ind +1], seg[2*ind+2]);}

ll maxquery(ll ind , ll low , ll high , ll l  , ll r){
if(low>=l and high<=r ) return seg[ind];
if(high<l or low>r) return INT_MIN;
ll mid = (low+high)/2;
ll left = maxquery(2*ind+1 , low, mid , l ,r);
ll right = maxquery(2*ind+2 , mid+1,high , l , r);
return max(left , right);

}

ll minquery(ll ind , ll low , ll high , ll l  , ll r){
if(low>=l and high<=r ) return seg[ind];
if(high<l or low>r) return INT_MAX;
ll mid = (low+high)/2;
ll left = minquery(2*ind+1 , low, mid , l ,r);
ll right = minquery(2*ind+2 , mid+1,high , l , r);
return min(left , right);
}

// Build the lazy segment tree
void buildlazy(vector<ll>& arr, int node, int start, int end) {
    if (start == end) {
        seg[node] = arr[start];  // Leaf node: assign the array value
    } else {
        int mid = (start + end) / 2;
        buildlazy(arr, 2 * node + 1, start, mid);      // Build left subtree
        buildlazy(arr, 2 * node + 2, mid + 1, end);    // Build right subtree
        seg[node] = seg[2 * node + 1] + seg[2 * node + 2];  // Internal node sum
    }
}

// Update the segment tree in a range with lazy propagation
void update_range(int node, int start, int end, int l, int r, ll val) {
    // Propagate any pending updates
    if (lazy[node] != 0) {
        seg[node] += (end - start + 1) * lazy[node];  // Update the current node
        if (start != end) {  // If not a leaf node, propagate to children
            lazy[2 * node + 1] += lazy[node];  // Mark lazy for left child
            lazy[2 * node + 2] += lazy[node];  // Mark lazy for right child
        }
        lazy[node] = 0;  // Clear the lazy value for this node
    }

    // Out of range case
    if (start > end || start > r || end < l)
        return;

    // Complete overlap case
    if (start >= l && end <= r) {
        seg[node] += (end - start + 1) * val;  // Apply update to the current node
        if (start != end) {  // If not a leaf node, propagate to children
            lazy[2 * node + 1] += val;  // Lazy update for left child
            lazy[2 * node + 2] += val;  // Lazy update for right child
        }
        return;
    }

    // Partial overlap case: update both left and right children
    int mid = (start + end) / 2;
    update_range(2 * node + 1, start, mid, l, r, val);      // Update left child
    update_range(2 * node + 2, mid + 1, end, l, r, val);    // Update right child
    seg[node] = seg[2 * node + 1] + seg[2 * node + 2];      // Update current node
}

// Query the sum in a range with lazy propagation
ll query_rangelazy(int node, int start, int end, int l, int r) {
    // Propagate any pending updates
    if (lazy[node] != 0) {
        seg[node] += (end - start + 1) * lazy[node];  // Apply pending update
        if (start != end) {  // If not a leaf node, propagate to children
            lazy[2 * node + 1] += lazy[node];  // Propagate to left child
            lazy[2 * node + 2] += lazy[node];  // Propagate to right child
        }
        lazy[node] = 0;  // Clear lazy value for this node
    }

    // Out of range case
    if (start > end || start > r || end < l)
        return 0;

    // Complete overlap case
    if (start >= l && end <= r)
        return seg[node];

    // Partial overlap case: query both left and right children
    int mid = (start + end) / 2;
    ll p1 = query_rangelazy(2 * node + 1, start, mid, l, r);      // Query left child
    ll p2 = query_rangelazy(2 * node + 2, mid + 1, end, l, r);    // Query right child
    return p1 + p2;  // Return the sum of both queries
}

char mirrorCharacter(char ch) {
    if (std::islower(ch)) {
        return 'a' + ('z' - ch);  // Mirror for lowercase letters
    } else if (std::isupper(ch)) {
        return 'A' + ('Z' - ch);  // Mirror for uppercase letters
    } else {
        return ch;  // Return the character as is if it's not a letter
    }
}


void extendgcd(ll a, ll b, ll*v) {
    if (b == 0) {
        v[0] = 1; v[1] = 0; v[2] = a; 
        return;
    } 
    extendgcd(b, a % b, v); 
    ll x = v[1]; v[1] = v[0] - v[1] * (a / b); v[0] = x; 
    return;
}


ll expo(ll a, ll b, ll mod) {
        
    // it will return (a^b)%(1e9+7)    

    ll res = 1;
    while (b > 0) {
        if (b & 1)res = (res * a) % mod; 
        a = (a * a) % mod; b = b >> 1;
    } 
    return res;
}

 
ll mminv(ll a, ll b) {
    ll arr[3]; 
    extendgcd(a, b, arr); 
    return arr[0];
}  //for non prime b
 
ll mminvprime(ll a, ll b) {
    return expo(a, b - 2, b);
}
 
ll mod_add(ll a, ll b, ll m) {
    a = a % m; b = b % m; 
    return (((a + b) % m) + m) % m;
}
 
ll mod_mul(ll a, ll b, ll m) {
    a = a % m; b = b % m; 
    return (((a * b) % m) + m) % m;
}
 
ll mod_sub(ll a, ll b, ll m) {
    a = a % m; b = b % m; 
    return (((a - b) % m) + m) % m;
}
 
ll mod_div(ll a, ll b, ll m) {
    a = a % m; b = b % m; 
    return (mod_mul(a, mminvprime(b, m), m) + m) % m;
}  //only for prime m 

ll gcdofvector(vector<ll>&v){
// return gcd of all elements of vector
ll answ = 0;
for(ll i=0;i<v.size();i++){
    answ = __gcd(v[i],answ);
    if(answ==1) {
        return 1;
    }
}
if(answ==0) return -1;
return answ;
}

long long lcm_ofARRAY( vector<int>& arr) {
    int lcm = arr[0];
    for (int i = 1; i < arr.size(); ++i) {
        int current = arr[i];
        // LCM(a, b) = (a * b) / GCD(a, b)
        lcm = (lcm * current) / __gcd(lcm, current);
    }
    return lcm;
}




int maxlength2( vector<ll>&v , ll k){
// return maxlength of a subarray with sum == k
// methd1 most optimal way by striver;
ll left = 0 , right = 0;
ll sum = v[0];
ll maxi = 0;
ll n = v.size();
while(right<n){

while(left<=right and sum>k){
sum = sum - v[left];
left++;
}

if(sum==k){
    maxi = max(maxi , right - left +1 );
}
right++;
if(right<n){
    sum+=v[right];
}


}

return maxi;

// // methd 2 
// map<ll,ll>m;
// ll l=0;
// m[0]=-1;
// ll sum =0;
// for(ll i=0;i<v.size();i++){
//     sum+=v[i];
//     if(m.find(sum-k)!=m.end()){
//         l = max(l , i-m[sum-k]);
//     }
//     if(m.find(sum)==m.end()){
//         m[sum] = i;
//     }
// }

// return l;

/*
same approach but style diff by himanshu gupta 
ll n,k;
cin>>n>>k;
vector<ll>v(n);
read(v,n);

vector<ll>pre(n+1);
pre[0] = 0;
for(ll i=1;i<n+1;i++){
    pre[i] = pre[i-1]+v[i-1];
}

map<ll,ll>mp;
for(ll i=0;i<n+1;i++){
     mp[pre[i]] = i;
    
}

ll length = 0;
for(int i= 0; i<n+1;i++){
    if(mp.find(pre[i]+k)!=mp.end()){
        length = max(length , mp[pre[i]+k] - i);
    }
}

cout<<length<<nl;



*/
}

ll count_subarrays(vector<ll>&v , ll k){
// return no of subarrays with sum = k;
ll n = v.size();
ll cnt = 0;
map<ll,ll>mp;
mp[0] = 1;
vector<ll>pre(n);
pre[0] = v[0];
for(ll i=1;i<n;i++){
    pre[i] = pre[i-1]+ v[i];
}
for(int i=0;i<n;i++){
if(mp.find(pre[i] - k)!=mp.end()){
    cnt+= mp[pre[i]- k];
}
mp[pre[i]]++;
}

return cnt;


}


int maxlength(vector<ll>&v, ll k){
// return maxlength of a subarray with sum atmost k
ll sum = 0;
ll n = v.size();
ll cnt = 0;
ll p= 0;
ll maxi = INT_MIN;
for(ll i=0;i<n;i++){
sum+=v[i];
if(sum<=k) {cnt++;
maxi = max(cnt,maxi);}
else{
    sum = sum - v[p];
    p++;
    maxi = max(maxi , cnt);
}
}

return maxi;

}

ll mex(vector<ll> & A) {
    set<int> b(A.begin(), A.end());

    int result = 0;
    while (b.count(result))
        ++result;
    return result;
}


string toUpperCase(const string &s) 
{ string k = ""; for (char c : s) k += toupper(c); return k; }


string toLowerCase(const string &s) 
{ string k = ""; for (char c : s) k += tolower(c); return k; }


vector<ll>permuation(vector<ll>&v){
    next_permutation(v.begin(),v.end());
    return v;
}

vector<ll> findDivisors(ll n){
vector<ll> divisors;
for (ll i = 1; i*i<=(n); ++i) {if (n % i == 0) {divisors.push_back(i);
if (i != n / i) {divisors.push_back(n / i);}}}return divisors;}


// function to get the index of sub in str
int isSubstring(string sub, string str)
{
    // using find method to check if sub is a substring of str
    if (str.find(sub) != string::npos)
        return str.find(sub);
    return -1;
}

ll getOR(const ll L,const ll R){
    //  agr L = 3 hein and R=8 to yeh 3|4|5|6|7|8 return krega where | is bitwise or 
    ll ans = L|R;
    if(L==R)
        return ans;
    ll cur = max(L,1LL);
    while(cur<R){
        ans|=cur;
        const ll b = cur&(-cur);
        if(cur+b-1<=R)
            ans|=cur+b-1;
        cur+=b;
    }
    cur=R;
    while(cur>L){
        ans|=cur;
        const ll b = cur&(-cur);
        if(cur-1>=L)
            ans|=cur-1;
        cur-=b;
    }
    return ans;

    // while calling function use this     cout<<getOR(max(a,0LL),b)<<endl;

}

ll getAND (ll l , ll r){
// it means if l=4 and r = 7 it returns 4&5&6&7
//Bitwise AND of Numbers Range  Leetcode 201 mik
while(r>l){
r = (r & (r-1));
}
return r;
}

int XOR_from_1toX(int x){ // if x=4 then return 1^2^3^4

    if(x%4==1) return 1;
    else if(x%4==2) return x+1;
    else if(x%4==3) return 0;
    else return x; 
    }
    
int XOR_from_LtoR(int L , int R){
int ans = XOR_from_1toX(L-1) ^ XOR_from_1toX(R);
return ans;
    }


    
ll getor(const vector<ll> &arr) { ll result = 0; for (ll num : arr) result |= num; return result; }
ll getxor(const vector<ll> &arr) { ll result = 0; for (ll num : arr) result ^= num; return result; }
ll getand(const vector<ll> &arr) { ll result = ~0; for (ll num : arr) result &= num; return result; }

int traversal_from_last_bit(int x , int y){
	   int ans=1;
	   int p=1;
	   for (int i=0;i<32;i++) {
	       int l=x>>i;
	       l&=1;
	       int r=y>>i;
	       r&=1;
	       
	       if (l!=r) {
	           break;
	       }
	       ans+=p;
	       p*=2;
	   }

return ans;
}


string decimal_to_binary(int x){

string s = "";

while(x!=0){
    if(x%2==1) s+='1';
    else s+='0';
    x = x/2;
}
reverse(s.begin(),s.end());
return s;

}

int set_ith_bit(int x , int i){ // make ith bit 1
int ans = x|(1<<i);
return ans;
}

int offset_ith_bit(int x, int i){  // make ith bit 0
int ans = x & ~(1<<i);
return ans ;
}

int reverse_ith_bit(int x , int i){
int ans = x ^ (1<<i);
return ans;
}

int remove_last_set_bit(int x , int i){
int ans = x&(x-1);
return ans;    
}

bool check_poweroftwo(int x){ // check whether x is power of 2 or not

if(  (x&(x-1)) == 0){
return true; // it is power of two eg 8 16 32
}
else return false; // it is not power of two eg 11 18 20

}

int count_set_bits(int x){ // it will return no of 1 in binary representation of x

ll cnt = 0;
while(x>1){
cnt+= x&1;
x=x>>1;
}

if(x==1) cnt++;
return cnt;

}

int count_set_bits_methd2(int x){
    return __builtin_popcount(x);
}

ll max_factor(ll n , ll k ){
// refer D. Buying Shovels codeforces
ll mini = INT_MAX;
for(ll i=1;i*i<=n;i++){
    if(n%i==0){
    if(i<=k){
        mini = min(mini , n/i);
    }
    if(n/i<=k){
        mini = min(mini , i);
    }

    }
}
return mini;

}


int check_ith_bit(int x , int i){
int u = (x>>i);
if( (u&1) == 0){
    return 0;   // this means ith bit is zero 
}
else return 1;
}

ll msb(ll x){
// moving from left that position of bit which is 1...
for(int i=31;i>=0;i--){
    if( x& (1LL<<i)){
        return i;
        
    }
}
}

void generate_subsequences(ll indx , vector<ll>&ds , vector<ll>&v , ll n , vector<vector<ll>>&ans ){
if(indx == n){ 
ans.push_back(ds);
return;
}
ds.push_back(v[indx]);
generate_subsequences(indx+1,ds,v,n , ans);
ds.pop_back();
generate_subsequences(indx+1,ds,v,n , ans);

}

void subsequence_sum_is_k(ll indx , vector<ll>&ds , vector<ll>&v , ll n , ll k ,  vector<vector<ll>>&ans , ll sum){
if(indx==n){
    if(sum==k){
        ans.push_back(ds);
    }
    return;
}
ds.push_back(v[indx]);
sum+=v[indx];
subsequence_sum_is_k(indx+1 , ds , v , n, k , ans,sum);
ds.pop_back();
sum = sum - v[indx];
subsequence_sum_is_k(indx+1 , ds , v , n, k , ans,sum);


}

ll lcm(ll a, ll b){
    return (a*b)/(__gcd(a,b));
}


int binary_to_decimal(string x){

int size = x.length();
int p = 1, num = 0;
for(int i=size - 1; i>=0; i--){
    if(x[i]=='1') num+=p;

    p = p*2; 
}return num;
}

int lcm_generator(vector<ll>v , ll n){
ll lc = 1;
for(int i=0;i<n;i++){
    lc = lcm(lc,v[i]);
}
return lc;

}

void getPrime(ll p, map < ll, ll >&ma){ 
    // store count of all prime factors of number p in map ma
    while(p%2 == 0) {
        ma[2]++;
        p/=2;
    }
    for(ll i = 3; i <= sqrt(p); i++) {
        while(p%i == 0) {
            ma[i]++;
            p/=i;
        }
    }
    if(p > 1)
        ma[p]++;
}



bool isSubsequence(string s, string t) {

ll i = 0 , j = 0 ;
while(i<s.size() and j<t.size()){
if(s[i]==t[j]){
            i++;j++;}

        else j++;}

bool ans;
    if(i==s.size()){
        ans = true;
    }
    else ans = false;

    return ans;
        
    }



bool isPRIME(ll n){

if(n==1) return false;
for(int i=2;i*i<=n;i++){
    if(n%i==0) return false;

}

return true;

}

ll binarySearch(vector<ll>& vec, ll target) {
    ll left = 0;
    ll right = vec.size() - 1;
 
    while (left <= right) {
        ll mid = left + (right - left) / 2;
 
        if (vec[mid] == target) {
            return mid;
        }
 
        if (vec[mid] < target) {
            left = mid + 1;
        }
 
        else {
            right = mid - 1;
        }
    }
 
    return -1;
}
 

ll ceilfun(ll a, ll b){
ll ans;
if(a%b==0){
ans = a/b;
}
else ans = a/b +1 ;
return ans;
}

ll power(ll a, ll b)
{
    int result = 1;
    while (b) {
        if (b & 1)
            result = (result * a) % MOD;
        a = (a * a) % MOD;
        b >>= 1;
    }
    return result;
}

ll bigsum(vector<ll>&v , ll n){
    ll sum = 0;
    	for(auto e:v){
		sum=((sum+e)%MOD+((e/MOD+1)*MOD))%MOD;
	}
    return sum;

}

ll noOfsetbits(ll x){
    ll ans = __builtin_popcount(x);
    return ans;
}

ll trailingzeroes(ll x){
    ll o = __builtin_ctz(x);
    return o;
}



ll maxlengthofsubsequnce(string a, string b){
// max length of a common subsequence of both a and b
// eg a = edrecg and b = acdgef
// maxlength of subseqence of b i.e (de) occurs in a..hence ans = 2;

ll n = a.size();
ll m = b.size();
ll ans = 0;
for(ll i=0;i<m;i++){
ll start = i;
ll cnt =0;
for(ll j=0;j<n;j++){
if(b[start]==a[j]){
    cnt++;
    start++;
}
}
ans = max(cnt,ans);
}

return ans;
}


// map<ll,ll>mp;
// for(auto ele:v){
//     mp[ele]++;
// }


ll countodd(ll l , ll r){
// it will return no of odd numbers between l and r including both l and r
// eg l = 3 , r = 8 // no of odd no between 3 and 8 is = 3 (i.e 3,5,7);
ll cnt;
if(l%2==1){
cnt = (r-l)/2 +1;
}
else cnt = (r-l +1 )/2;

return cnt;
}

vector<pair<pair<ll,ll>,ll>> overlap( vector<pair<ll,ll>>&a , ll n , ll d , ll k){
    // following 1 based indexing
    // coder abhi Codeforces Round 974 (Div 3) ques D
sort(a.begin(), a.end()); 

vector<pair<pair<ll,ll>,ll>>ans;
int j = 0;
    priority_queue<int, vector<int>, greater<int>> pq;
    for (int i = 1; i <= n - d + 1; i++) {
        // i to i+d-1
        while (j < k && a[j].first <= i + d - 1) {
            pq.push(a[j].second); // k times in total -> dlogd
            j++;
        }
        while (pq.size() && pq.top() < i) {
            pq.pop(); // k times in total -> dlogd
        }
        int c = pq.size();
        auto u = make_pair(i,i+d-1);
        auto g = make_pair(u,c);
        ans.push_back(g);

}
return ans;
}


ll lpsKPM(string &s){
vector<ll>lps(s.size(), 0);
ll pre = 0 , suff = 1;
while(suff<s.size()){

if(s[pre]==s[suff]){
    lps[suff] = pre +1; 
    pre++;
    suff++;

}
else{

if(pre==0){
    lps[suff] = 0 ;
    suff++;
}
else{
    pre = lps[pre-1];
}

}

return lps[lps.size()-1];
}
}


vector<ll> lpsKPMs(string &s){
vector<ll>lps(s.size(), 0);
ll pre = 0 , suff = 1;
while(suff<s.size()){

if(s[pre]==s[suff]){
    lps[suff] = pre +1; 
    pre++;
    suff++;

}
else{

if(pre==0){
    lps[suff] = 0 ;
    suff++;
}
else{
    pre = lps[pre-1];
}

}

return lps;
}
}

vector<ll>Zalgorithm(string s){
vector<ll>z(s.size(),0);
ll l = 0 , r = 0;
for(ll i=1;i<s.size();i++){
    if(i<r){
        z[i] = z[i-l];
        if(i+z[i]>r){
            z[i] = r - i;
        }
    }

    while(i+z[i]<s.size() and s[z[i]]==s[i+z[i]]){
        z[i]++;
    }
    if(i+z[i]>r){
        l= i ; r = i+z[i];
    }
}

return z;
}



ll substringCHeck(string &a , string &b){
// check b is substring of a ??
// return index of a where b is occuring
vector<ll>lps(b.size(),0);
ll pre = 0 , suff = 1;
while(suff<b.size()){

if(b[pre]==b[suff]){lps[suff] = pre +1; pre++;suff++;}
else{
if(pre==0){lps[suff] = 0 ;suff++;}
else{pre = lps[pre-1];}}}

int first = 0 , second = 0;
while(first<a.size() and second<b.size()){
if(a[first] == b[second]){
first++ ; second++;
}
else{if(second==0){first++;}else{second = lps[second - 1];}}
}
if(second == b.size()){ return first - second;}
else{return - 1;}

}

vector<ll> preffix (vector<ll>&v){
ll n = v.size();
vector<ll>pre (n);
pre[0] = v[0];
for(ll i=1;i<n;i++){
    pre[i] = pre[i-1] + v[i];
}
return pre;
}

void subsetsum ( vector<ll>&v , ll l , ll r, unordered_map<ll,ll>&mp , ll sum , ll x){
// refer meet in the middle algo by bharat khanna.. used in cses prob set
// store count of possible sums (<=x) of generated subsets( 2^n) of a vector in unordered map ..
if(sum>x) return;
if(l>r or sum==x){
    mp[sum]++; return;
}
subsetsum(v,l+1,r,mp,sum,x);
if(v[l]+sum<=x){
subsetsum(v,l+1,r,mp,sum+v[l],x);
}
}

ll ncr(ll n , ll r){

if(n<r) return 0;
if(n- r< r) r = n - r;
int dpn[r+1];
memset(dpn , 0 , sizeof(dpn));
dpn[0] = 1;
for(ll i=1;i<=n;i++){
    for(ll j = min(r,i) ; j>0;j--){
        dpn[j] = (dpn[j] + dpn[j-1])%MOD;
    }
}
return dpn[r];
}


vector<ll> suffix( vector<ll>& v){

ll n = v.size();
vector<ll>suff(n);
suff[n-1] = v[n-1];
for(ll i=n-2;i>=0;i--){
    suff[i] = suff[i+1] + v[i];
}

return suff;
}

vector<ll> rotateLEFT(vector<ll>&v , ll k){
// rotate array k times left ...
// old vec = 1 2 3 4 5
// rotate k = 3 times left 
// new vec = 4 5 1 2 3
rotate(v.begin(), v.begin()+k, v.end());
return v;
}

vector<ll> rotateRIGHT( vector<ll>&v , ll k){
// rotate array k times right ...
// old vec = 1 2 3 4 5
// rotate k = 3 times right
// new vec =  3 4 5 1 2
rotate(v.begin(), v.begin()+v.size()-k, v.end());
return v;
}




string decimalToBinary(int n) {
    string result = "";
    // if u want 64 bits then replace 31 by 61
    for (int i = 31; i >= 0; i--) {
        int bit = (n >> i) & 1;  
        result.push_back(bit + '0');
    }
    return result;
}

bool subarraysumequalK(vi &v , ll k){
// check if there exists a subarray whose sum == k.    
ll n  = v.size();
ll i = 0 , j = 0;
ll sum = 0;
while(i<n){
while(j<n and sum<k){
sum+=v[j];
j++;
}
if(sum==k){ return true;}
sum = sum  - v[i];
if(sum==k){ return true;}
i++;
}
return false;
}



// very useful function
ll fast_exponentiation(ll b, ll exp) {
    ll result = 1;
    b = b % MOD;
    while (exp > 0) {
        if (exp % 2 == 1) {
            result = (result * b) % MOD;
        }
        b = (b * b) % MOD;
        exp = exp / 2;
    }
    return result;
}

bool comp(const pair<int, int>& a, const pair<int, int>& b) {
    if (a.first == b.first) {
        // If first elements are equal, sort by second element in decreasing order
        return a.second > b.second;
    }
    // Otherwise, sort by first element in increasing order
    return a.first < b.first;
}

ll findMinimumSum(vector<ll>& nums) {
    // subarray with lowest sum just similar and opposite to kadanes algorithm
    ll currentSum = 0;
    ll minSum = INT_MAX;

    for (int num : nums) {
        currentSum += num;
        minSum = std::min(minSum, currentSum);
        if (currentSum > 0) {
            currentSum = 0;
        }
    }

    return minSum;
}

string findecimalToBinary(ll decimal_number) {
    bitset<64> binary(decimal_number);
    return binary.to_string();
}
 
ll finbinaryToDecimal(string& binary_string) {
    bitset<64> binary(binary_string);
    return binary.to_ullong();
}

ll kadanes(vector<ll>&v, ll n){

ll sum = 0;
ll maxi = INT_MIN;
for(ll i=0;i<n;i++){
sum+=v[i];
maxi = max( maxi , sum);
if(sum<0){
	sum=0;
}}

ll ans = max(maxi,0LL);
return ans;

}

long long numberOfDivisors(long long num) {
    long long total = 1;
    for (int i = 2; (long long)i * i <= num; i++) {
        if (num % i == 0) {
            int e = 0;
            do {
                e++;
                num /= i;
            } while (num % i == 0);
            total *= e + 1;
        }
    }
    if (num > 1) {
        total *= 2;
    }
    return total;
}
const int N = 1e7;  // Maximum limit
vector<bool> is_prime(N + 1, true);  // Boolean sieve array

void sievePRIYANSH(int n) {
    is_prime[0] = is_prime[1] = false;  // 0 and 1 are not prime
    for (int i = 2; i * i <= n; i++) {
        if (is_prime[i]) {
            for (int j = i * i; j <= n; j += i) {
                is_prime[j] = false;
            }
        }
    }
}


unsigned int flipBits(unsigned int x) {
    // it flips the bits of x; // supppose x = 5 (101) .. it will return 2(010);
    if (x == 0) return 1;  
    int num_bits = log2(x) + 1;  
    unsigned int mask = (1U << num_bits) - 1;  
    return (~x) & mask;  
}
bool isPalindrome(string s)
{
    int i = 0, j = s.size()-1;
    while(i<=j)
    {
        if(s[i] != s[j]) return false;
        i++, j--;
    }
    return true;
}



void solve() {

string p ,s ;
cin>>p>>s;

int n = p.size();
int m = s.size();
int i =0 , j =0 ;

if(p==s){
    py;
    return;
}

vector<int> sl;
vector<int> sr;
vector<int> pl;
vector<int> pr;





}



int main(){
// cin.tie(0)->sync_with_stdio(0);
ll t = 1;
cin>>t;

while(t--){
solve();    
}
}



// a<<b == a * 2^b;  left shift
// a>>b = a / (2^b); right shift
 
// ll n; cin>>n; vector<ll>v(n); read(v,n);

// vector<ll>s(n);
// for(auto &i : s) cin >> i;


// XOR is sometimes called bitwise exclusive or // for reference see prob E vlad and a pair of numbers


// how to handle edge cases in 2d matrix
//   for(ll i=0; i<n; i++){
//         for(ll j=0; j<m; j++){
//             ll a = (i>=1)?array[i-1][j]:-1;
//             ll b = (i<n-1)?array[i+1][j]:-1;
//             ll c = (j>=1)?array[i][j-1]:-1;
//             ll d = (j<m-1)?array[i][j+1]:-1;
//             if(array[i][j]>max({a,b,c,d})) array[i][j]=max({a,b,c,d});}}

/*
how to input 2d vector
ll n; cin>>n;
vector<vector<char>>v(n);

for(ll i=0;i<n;i++){
for(ll j=0;j<n;j++){
char val;
cin>>val;
v[i].push_back(val);

}*/

// if(x&1==1){
//cout<<"odd";
//} 

// format of min and max
// min({c, m, (c + m + x) / 3})

//cout<<fixed<<setprecision(19)<<pi<<nl;

// for any two numbers a,b>0 we can say that -->
// a+b = a^b + 2(a&b);
// where ^ is  xor , & is and operator

// count characters
//string s;
// cin>>s;
// int a = count(s.begin(),s.end(),'1');
// cout<<a<<nl;