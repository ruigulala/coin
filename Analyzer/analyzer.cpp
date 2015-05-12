#include "stdio.h"
#include "string.h"
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <fcntl.h>
#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include "general_types.H"

#include <iostream>
#include <climits>
#include <vector>
#include <map>
#include <algorithm>

/* ----------------Global Variables--------------- */
/* Store all the "dynamic" query ins */
std::map<uint32_t, std::vector<uint64_t> > queryIns;
/* Store all the trace start index for each thread */
std::vector<uint64_t> threadStartIndex;
/* Store the lockset for each LOCK and UNLOCK ins */
std::map<uint64_t, std::vector<uint64_t> > lockset;
std::vector<uint64_t> dummyLockset;
/* Barrier index per each thread */
std::map<uint64_t, std::vector<uint64_t> > barrIndex;
/* Lock and unlock index per each thread */
std::map<uint64_t, std::vector<uint64_t> > lockIndex;

/* The number of entries */
uint64_t size;

extern void dumpTimestamp(uint16_t * ts);

// Find the dynamic matching entry for the static ins
void find_ins(const recentry_t * buffer, 
    std::map<uint32_t, uint32_t> * staticIns)
{
  uint64_t i = 0;
  std::map<uint32_t, uint32_t>::iterator it;
  for(i = 0; i < size; i++)
  {
    it = staticIns->find(buffer[i].info.access.ip);
    if(it != staticIns->end()) {
      assert(buffer[i].op == READ_OP);
      queryIns[it->first].push_back(i);
      it->second++;
    }
  }
  for(it = staticIns->begin(); it != staticIns->end(); it++)
  {
    if(it->second == 0)
      std::cerr << "Can't find dynamic mapping for ins:0x" <<std::hex<< it->first << std::endl;
  }
}

// Compute the start index for each thread and compute the lockset
void pre_compute(const recentry_t * buffer)
{
  uint8_t curThread = 0;
  std::vector<uint64_t> curLock;
  uint64_t i = 0;
  threadStartIndex.push_back(0);
  for( i = 0; i < size; i++)
  {
    if(buffer[i].thread != curThread) {
      // Make sure the log is in ascending order
      assert(buffer[i].thread == curThread + 1);
      threadStartIndex.push_back(i);
      curThread++;
    }
    if(buffer[i].op == LOCK_OP) {
      curLock.push_back(i);
      lockset[i] = curLock; 
      lockIndex[buffer[i].thread].push_back(i);
    }
    else if(buffer[i].op == UNLOCK_OP) {
      std::vector<uint64_t>::iterator it;
      for(it = curLock.begin(); it != curLock.end(); it++) {
        if(buffer[*it].info.lock.lock == buffer[i].info.lock.lock) {
          curLock.erase(it);
          break;
        }
      }
      // An unlock must follows a lock
      //assert(it == curLock.end());
      lockset[i] = curLock;
      lockIndex[buffer[i].thread].push_back(i);
    }
    else if(buffer[i].op == BARRIER_OP) {
      barrIndex[buffer[i].thread].push_back(i);
    }
  }
}

void test_pre_compute()
{
  std::cout << "First dump threadStartIndex" << std::endl;
  std::vector<uint64_t>::iterator it;
  uint8_t i = 0;
  for(it = threadStartIndex.begin(); it != threadStartIndex.end(); it++) {
    std::cout << "Thread " << i << " starts at " << *it << std::endl;
    std::cout << "Barrier Index for Thread " << i << std::endl;
    std::vector<uint64_t>::iterator it1;
    for(it1 = barrIndex[i].begin(); it1 != barrIndex[i].end(); it1++) {
      std::cout << *it1 << " ";
    }
    std::cout << std::endl;
    std::cout << "Lock and Unlock Index for Thread " << i << std::endl;
    for(it1 = lockIndex[i].begin(); it1 != lockIndex[i].end(); it1++) {
      std::cout << *it1 << std::endl;;
      std::cout << "Lockset is:" << std::endl;
      std::vector<uint64_t>::iterator it2;
      for(it2 = lockset[*it1].begin(); it2 != lockset[*it1].end(); it2++) {
        std::cout << *it2 << " "; 
      }
      std::cout << std::endl;
    }
    i++;
  }
}

/* Return the ins's timestamp */
uint16_t * getTimestamp(const recentry_t * buffer, const uint64_t start_ins)
{
  assert(buffer[start_ins].op == WRITE_OP || buffer[start_ins].op == READ_OP);
  assert(start_ins <= size);
  uint64_t end_index;
  // Find the trace start of the thread
  std::vector<uint64_t>::iterator it;

  //std::cout << "Dump threadStartIndex:" << std::endl;
  //for(it = threadStartIndex.begin(); it != threadStartIndex.end(); it++)
  //std::cout << *it << " ";
  //std::cout << std::endl;
  
  for(it = threadStartIndex.begin(); it != threadStartIndex.end(); it++)
  {
    // If we reach the last thread start
    if((it + 1) == threadStartIndex.end())
    {
      end_index = *it;
    }
    else if(*it <= start_ins && *(it + 1) > start_ins)
    {
      end_index = *it;
      break;
    }
  }
  uint64_t i;
  uint16_t * ts = (uint16_t*)calloc(BARRNUMS + 1, sizeof(uint16_t));     
  for(i=start_ins - 1; i != static_cast<uint64_t>(end_index-1); i--)
  {
    if(buffer[i].op == BARRIER_OP) 
    {
      int skew = 8;
      int ts_i = 0;
      while(skew >= 0)
      {
        ts[ts_i++] = buffer[i - skew].info.barrier.ts0;
        ts[ts_i++] = buffer[i - skew].info.barrier.ts1;
        ts[ts_i++] = buffer[i - skew].info.barrier.ts2;
        ts[ts_i++] = buffer[i - skew].info.barrier.ts3;
        skew--;
      }
      break;
    }
  }
  if(i == static_cast<uint64_t>(end_index - 1)) {
    //std::cerr << "Error: Missing Timestamp for Thread " 
    //  << buffer[start_ins].thread << std::endl;
    //abort();
  }

  return ts;
}

/* Return the ins's lockset */
std::vector<uint64_t> * getLockset(const recentry_t * buffer, 
    const uint64_t start_ins)
{
  uint64_t end_index;
  // Find the trace start of the thread
  assert(start_ins <= size);
  std::vector<uint64_t>::iterator it;
  for(it = threadStartIndex.begin(); it != threadStartIndex.end(); it++)
  {
    // If it's the last thread
    if((it + 1) == threadStartIndex.end())
    {
      end_index = *it;
    }
    else if(*it <= start_ins && *(it + 1) > start_ins)
    {
      end_index = *it;
      break;
    }
  }

  uint64_t i;
  for(i = start_ins - 1; i != static_cast<uint64_t>(end_index-1); i--)
  {
    if(buffer[i].op == LOCK_OP || buffer[i].op == UNLOCK_OP)
    {
      return &lockset[i];  
    }
  }
  if(i == static_cast<uint64_t>(end_index - 1)) {
    //std::cerr << "Warning: No Lock or Unlock operations being performed ahead" 
    //<< " " << start_ins<< std::endl;
  }
  return &dummyLockset;
}

// Given a shared variable read ins, find the W ins backwards
uint64_t findW(const recentry_t * buffer, const uint64_t start_ins)
{
  assert(buffer[start_ins].op == READ_OP);
  // 1.1 Need to be a write op
  // 1.2 Need to access the same mem location as read op
  // 1.3 The value of the write need to be the same as read op
  // 2. Put all to a vector and compare those timestamp to r
  // 3. Compare all to the last, pop_back ...
  // 4. Pick one from what's left

  uint64_t i = size - 1;
  std::vector<uint64_t> candidateW;
  uint16_t * r_ts;
  r_ts = getTimestamp(buffer, start_ins);
  for(; i != static_cast<uint64_t>(-1); i--)
  {
    if(buffer[i].op != WRITE_OP) continue;
    if(buffer[i].info.access.addr != buffer[start_ins].info.access.addr) 
      continue;
    if(buffer[i].info.access.val != buffer[start_ins].info.access.val)
      continue;
    // r.ts < w.ts -> false
    uint16_t * w_ts;
    w_ts = getTimestamp(buffer, i);
    if(r_ts[buffer[start_ins].thread] < w_ts[buffer[start_ins].thread]) {
      free(w_ts);
      continue;
    }
    // Prune out the ins after start_ins within the same thread
    if(buffer[i].thread == buffer[start_ins].thread)
      if(i > start_ins) {
        free(w_ts);
        continue;
      }
    free(w_ts);
    candidateW.push_back(i);
  }
  if(candidateW.size() == 0)
  {
    std::cerr << "Can't find the corresponding W ins"; 
    std::cerr << "for Ins:" << start_ins << " Op:" 
      << buffer[start_ins].op << std::endl; 
    free(r_ts);
    abort();
    return 0;
  }
  free(r_ts);  
  // Dump the vector
  //std::vector<int>::iterator it;
  //for(it = candidateW.begin(); it != candidateW.end(); it++)
    //std::cout << *it << " ";
  //std::cout << std::endl; 

  if(candidateW.size() == 1)
    return candidateW[0];

  // Find the lastest w ins
  // Get the timestamp of all the w candidates
  uint16_t ** w_ts = (uint16_t**)calloc(candidateW.size(), sizeof(uint16_t *));
  int w_vec_i = 0;
  for(w_vec_i = 0; w_vec_i < candidateW.size(); w_vec_i++)
  {
    w_ts[w_vec_i] = (uint16_t*)calloc(BARRNUMS + 1, sizeof(uint16_t));
    w_ts[w_vec_i] = getTimestamp(buffer, candidateW[w_vec_i]);
  }

  for(w_vec_i = 0; w_vec_i < candidateW.size() - 1; w_vec_i++)
  {
    int i_tmp = 0;
    for(i_tmp = w_vec_i + 1; i_tmp < candidateW.size(); i_tmp++)
    {
      // if w_vec_i.ts < i_tmp.ts
      if(w_ts[w_vec_i][buffer[candidateW[w_vec_i]].thread] < 
          w_ts[i_tmp][buffer[candidateW[w_vec_i]].thread])
      {  
        break;
      }
    }
    if(i_tmp == candidateW.size()) {
      // Free the memory
      for(i_tmp = 0; i_tmp < candidateW.size(); i_tmp++)
      {
        free(w_ts[i_tmp]);
      }
      free(w_ts);
      return candidateW[w_vec_i];
    }
  }
  std::cerr << "ERROR: candidates disappeared." << std::endl;
  abort();
  return 0;
}

bool isWPrime(const recentry_t * buffer, const uint64_t r_ins, 
    const uint64_t w_ins, const uint64_t w_p_ins)
{
  assert(w_ins != w_p_ins);
  // 0 w and w' need to access the same mem location
  if(buffer[w_ins].info.access.addr != buffer[w_p_ins].info.access.addr)
    return false;

  // Obtain the timestamp
  uint16_t * r_ts = getTimestamp(buffer, r_ins);
  uint16_t * w_ts = getTimestamp(buffer, w_ins);
  uint16_t * w_p_ts = getTimestamp(buffer, w_p_ins);
  
  // 1.1 r.time_stamp < w'.time_stamp, r and w' not same thread
  if(buffer[r_ins].thread != buffer[w_p_ins].thread) {
    if(r_ts[buffer[r_ins].thread] < w_p_ts[buffer[r_ins].thread]) { 
      free(r_ts);
      free(w_ts);
      free(w_p_ts);
      return false;
    }
  }
  // 1.2 r and w' in same thread
  else {
    if(r_ins < w_p_ins) {
      free(r_ts);
      free(w_ts);
      free(w_p_ts);
      return false;
    }
  }
  // 2.1 w′.time-stamp < w.time-stamp < r.time-stamp then (different thread)
  if(buffer[w_p_ins].thread != buffer[w_ins].thread) {
    if(w_p_ts[buffer[w_p_ins].thread] < w_ts[buffer[w_p_ins].thread] &&
        w_ts[buffer[w_ins].thread] < r_ts[buffer[w_ins].thread]) {
      free(r_ts);
      free(w_ts);
      free(w_p_ts);
      return false;
    }
  }
  // 2.2 w′.time-stamp < w.time-stamp then (same thread)
  // w < r is enforced by findW
  else {
    if(w_p_ins < w_ins) {
      free(r_ts);
      free(w_ts);
      free(w_p_ts);
      return false;
    }
  }
  // 3. if w is executed before r in a critical section CS1,
  // w′ is in critical section CS2, CS1 and CS2 are from different threads,
  // and CS1 is mutually exclusive from CS2 then
  std::vector<uint64_t> * w_lockset, * r_lockset, * w_p_lockset;
  w_lockset = getLockset(buffer, w_ins);
  r_lockset = getLockset(buffer, r_ins);
  w_p_lockset = getLockset(buffer, w_p_ins);
  if(buffer[r_ins].thread == buffer[w_ins].thread) {
    if(buffer[r_ins].thread != buffer[w_p_ins].thread) {
      std::vector<uint64_t> cs1(20);
      std::vector<uint64_t> result(20);
      std::vector<uint64_t>::iterator it;
      it=std::set_intersection (w_lockset->begin(), w_lockset->end(),
          r_lockset->begin(), r_lockset->end(), cs1.begin());
      cs1.resize(it - cs1.begin());

      it=std::set_intersection (w_p_lockset->begin(), w_p_lockset->end(), 
          cs1.begin(), cs1.end(), result.begin());
      result.resize(it - result.begin());
      if(result.size() != 0) {
        free(r_ts);
        free(w_ts);
        free(w_p_ts);
        return false;
      }
    }
  }
  // 4.if w′ is executed before w in a critical section CS1, 
  // r is in critical section CS2, CS1 and CS2 are from different threads, 
  // and CS1 is mutually exclusive from CS2 then
  if(buffer[w_ins].thread == buffer[w_p_ins].thread) {
    if(buffer[r_ins].thread != buffer[w_ins].thread) {
      std::vector<uint64_t> cs1(20);
      std::vector<uint64_t> result(20);
      std::vector<uint64_t>::iterator it;
      //for(it = w_lockset->begin(); it != w_lockset->end(); it++)
        //std::cout << "L: "<< *it << std::endl;
      it=std::set_intersection (w_lockset->begin(), w_lockset->end(),
          w_p_lockset->begin(), w_p_lockset->end(), cs1.begin());
      cs1.resize(it - cs1.begin());

      it=std::set_intersection (r_lockset->begin(), r_lockset->end(), 
          cs1.begin(), cs1.end(), result.begin());
      result.resize(it - result.begin());
      if(result.size() != 0) {
        free(r_ts);
        free(w_ts);
        free(w_p_ts);
        return false;
      }
    }
  }
  free(r_ts);
  free(w_ts);
  free(w_p_ts);
  return true;
}

void dumpTimestamp(uint16_t * ts)
{
  int i = 0;
  std::cout << "Timestamp dump:" << std::endl;
  for(i = 0; i < BARRNUMS + 1; i++)
    std::cout << ts[i] << " ";
  std::cout << std::endl;
}

void dumpToVec(const recentry_t* rec)
{
  int i=0;
  printf("%d\t",(int)rec->thread);
  switch(rec->op){
    case READ_OP:
      printf("R\t");
      printf("0x%x\t0x%x",rec->info.access.ip,rec->info.access.addr);
      printf("\t%d",rec->info.access.reg);
      printf("\t%d",rec->mid);
      printf("\n");
      break;
    case WRITE_OP:
      printf("W\t");
      printf("0x%x\t0x%x",rec->info.access.ip,rec->info.access.addr);
      printf("\t%d",rec->info.access.reg);
      printf("\t%d", rec->mid);
      printf("\n");
      break;
    case BARRIER_OP:
      printf("B\t");
      printf("%d\t%d\t%d\t%d\n",(int)rec->info.barrier.ts0,(int)rec->info.barrier.ts1,
	  (int)rec->info.barrier.ts2, (int)rec->info.barrier.ts3);
      break;
    case LOCK_OP:
      printf("L\t");
      printf("0x%x\t%d\n",rec->info.lock.lock,rec->info.lock.instance);
      break;
    case UNLOCK_OP:
      printf("U\t");
      printf("0x%x\t%d\n",rec->info.lock.lock,rec->info.lock.instance);
      break;
    default:
      ;
  }
}

bool parseTraceLine(recentry_t * buf, long iadr, long dadr, long count)
{
  if((buf->op == READ_OP) || (buf->op == WRITE_OP))
  {
    if((iadr!=0) && ((long)buf->info.access.ip!=iadr)) return false;
    if((dadr!=0) && ((long)buf->info.access.addr!=dadr)) return false;
  }
  return true;
}

void readIns(char * ilistFile, std::map<uint32_t, uint32_t> * staticIns)
{
  FILE *ifp;
  uint32_t ins;
  ifp = fopen(ilistFile, "r");
  if (ifp == NULL) {
    fprintf(stderr, "Can't open input file in.list!\n");
    exit(1);
  }
  while (fscanf(ifp, "%x", &ins) != EOF) {
    (*staticIns)[ins] = 0;
  }
  return;
}
int main(int argc, char * argv[])
{
  //set default value:
  if(argc < 2){
    printf("Please type -h for help\n");
    return 0;
  }

  extern char * optarg;
  char ch;
  char tracefilename[100];
  char ilistFile[100];
  //long iaddr=0;
  long daddr=0;
  long count=0;
  strcpy(tracefilename,"temp");

  while ((ch = getopt(argc,argv,"i:d:f:c:h")) != -1){
    switch(ch){
      case 'f': strcpy(tracefilename,optarg);break;
      case 'd': daddr=strtoul(optarg,NULL,0);break;       //atoi(optarg);break;
      case 'c': count=strtoul(optarg,NULL,0);break;
      case 'i': strcpy(ilistFile, optarg);break;
      case 'h':
      default: 
        printf("-f tracefile name\n");
        printf("-d interesting data memory address\n");
        printf("-i interesting instruction address\n");
        printf("-c entry index [invalid in this version]\n");
        printf("-h help\n");
        return 0;
    }
  }

  int tracefile;
  struct stat st;
  recentry_t* buffer;
  printf("Display parameters:\n");
  printf("Trace file: %s\n", tracefilename);
  printf("Instruction file: %s\n", ilistFile);
  printf("Begin to analyze:\n");

  tracefile = open(tracefilename, O_RDWR);
  if(tracefile < 0){
    perror("Error opening file:");
    fprintf(stderr,"./ctdbg_s -f <filename> -i <instruction filter> -d <access-address filter>\n");
    return 0;
  }
  if(fstat(tracefile, &st) < 0){
    perror("Error stating file:");
    return 0;
  }
  buffer = (recentry_t *)mmap(0, (1 + st.st_size / 4096) * 4096, 
			      PROT_READ | PROT_WRITE, MAP_SHARED, tracefile, 0);

  size = st.st_size / sizeof(recentry_t);
  assert(size < ULLONG_MAX);

  if(buffer == (void *)-1){
    perror("Error with mmap:");
    return 0;
  }

  pre_compute(buffer);
  //test_pre_compute();

  std::map<uint32_t, uint32_t> staticIns;
  // Read instructions from a file
  readIns(ilistFile, &staticIns);
  find_ins(buffer, &staticIns);

  printf("Size of the file is %llu\n", size);
  /* Test findW() */
  std::map<uint32_t, std::vector<uint64_t> >::iterator it;
  std::vector<uint64_t>::iterator it2;
  for(it = queryIns.begin(); it != queryIns.end(); it++)
  {
    for(it2 = it->second.begin(); it2 != it->second.end(); it2++)
    {
      uint64_t tmp_w = findW(buffer, *it2);
      printf("T%u R:%llu[0x%x]  T%u W:%llu[0x%x]\n", buffer[*it2].thread, 
          *it2, buffer[*it2].info.access.ip, buffer[tmp_w].thread,
          tmp_w, buffer[tmp_w].info.access.ip);
      uint64_t i = 0; 
      //int progress = 0;
      for(i = 0; i < size; i++)
      {
        //if(i % (uint64_t)(size * 0.1) == 0) {
          //printf("%d%% is done.\n", 10 * progress);
          //progress++;
        //}
        if(buffer[i].op == WRITE_OP && i != tmp_w)
          if(isWPrime(buffer, *it2, tmp_w, i))
            printf("[RESULT]T%u R: %llu[0x%x] \tT%u W: %llu[0x%x] \tT%u W': %llu[0x%x]\n", 
                buffer[*it2].thread, 
                *it2, buffer[*it2].info.access.ip, buffer[tmp_w].thread, tmp_w, 
                buffer[tmp_w].info.access.ip, buffer[i].thread, i, 
                buffer[i].info.access.ip);
      }
    }
  }

  //uint64_t index = 0;
  //for(index = 0;index < size; index++){
    //std::cout << "Index:" << std::dec << index << std::endl;
    //dumpToVec(&buffer[index]);
  //}

  /* Test for getTimeStamp */
  //uint16_t * tmp = getTimestamp(buffer, 16);
  //dumpTimestamp(tmp);
  //free(tmp);

  //finish 
  msync(buffer, st.st_size, MS_SYNC);
  printf("done\n");
}
