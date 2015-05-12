/**********************************

  A general purpose Pin tracing tool

  What it can do:
  (1) trace the memory address , memory value, and the memory malloc id (i.e. malloc epoch)
  (2) thread id
  (2) trace the lock/unlock operations
  (3) trace other synchronization operations such as barrier, pthread_create/join

#include <stdio.h>
#ifndef __PINH
#define __PINH
#include "pin.H"
#endif

//#include <sys/types.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <unistd.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <map>
#include "assert.h"
#include <signal.h>
#include <ext/hash_map>
#include <iostream>
#include <fstream>
#include <sstream>
#include <pthread.h>

using namespace std;

#include "general_types.H"
#include "malloc_id.h"

#define STACK_LOWERBOUND 0x40000000
#define USER_LOWERBOUND  0x08000000
#define USER_UPPERBOUND  0x15000000


/* ===================================================================== */
/* Commandline Switches 
   -startin, -stopin, -sig, -rpc, -wpc, -o, -debug
   */
/* ===================================================================== */


bool GetArg_ul(UINT32 argc, char** argv, const char* argname, UINT32& arg, UINT32 default_val, UINT32 index);
bool GetArg(UINT32 argc, char** argv, const char* argname, string& arg, string default_val);

FILE *trace;
KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool",
    "o", "/dev/shm/conseq_looplog.out", "specify trace output file name");
// KNOB<string> KnobFunctionFile(KNOB_MODE_WRITEONCE, "pintool", 
// 			      "functionlist", "./function.addr", "specifiy trace output file name");
// map<unsigned long, unsigned long> map_function;
/*-----tracing data structure-------*/
#ifndef __LOGMACRO
#define LOGSIZE (4096)
#define SPARE (7)
#define __LOGMACRO
#endif


typedef struct writeLog{
  LEVEL_BASE::PIN_LOCK log_lock;
  recentry_t buffer[LOGSIZE+SPARE];
  int offset;
  int valid;
  int fd;
  int thread;
  int pid;
} writeLog_t;

char work_dir[1000];
writeLog_t logs[MAXTHREADS]; //pay attention, only MAXTHREADS can be recorded


/*-------Variables for barrier, lock tracing and time-stamp---------*/
map<UINT32,UINT32> osIdpinIdMap;
map<UINT32,uint16_t*> createMap; //thread-create timestamp
bool thread_init[MAXTHREADS];
LEVEL_BASE::PIN_LOCK createmLock; //protect createMap

static uint16_t zerots[BARRNUMS+1];
typedef uint16_t* ts_T;
typedef struct {
  uint8_t finish;   //index of the finished one
  uint8_t ongoing;  //index of the ongoing one
  uint16_t prog;    //on-going's progress
  ts_T ts[2];
} bts_T;
std::map<uint32_t,int> lock_map;
//<lock-mem-loc, dyn.-instance>
LEVEL_BASE::PIN_LOCK lockmapLock; //protect lock_map
std::map<uint32_t,bts_T> barr_map;
//<barr-mem-loc, time-stamp>
LEVEL_BASE::PIN_LOCK barrLock; //protect barr_map
uint16_t thread_ts[MAXTHREADS][BARRNUMS+1];  //store each thread's timestamp, no lock needed

/*----------ts_T unitility function------------------*/
inline void arr2ts(uint16_t* src, ts_T dst)
{
  for(int i = 0; i <= BARRNUMS; i++)
  {
    dst[i] = src[i];
  }
}
inline void ts2arr(ts_T src, uint16_t* dst)
{
  for(int i = 0; i <= BARRNUMS; i++)
  {
    dst[i] = src[i];
  }
}
/*------------------^^^^^^^^^^^^^^^---------*/

/*********************************************
 ****Utility functions to write log files
 ****NOTE: we do NOT assume any concurrent update!
 ******************************************/

int open_new_file(int pid, int thread){
  int res;
  char filestr[1100];
  //  sprintf(filestr, "%s/thread%05d-%02d.out", work_dir, pid, thread);
  sprintf(filestr, "/dev/shm/thread%05d-%02d.out", pid, thread);
  res = open(filestr, O_RDWR | O_CREAT | O_APPEND, 0644);
  if(res < 0){
    perror("cannot open tracing file:");
    //exit(-1);
  }
  return res;
}

#define flush_log(log) \
  do{ \
    GetLock(&log.log_lock, 1);\
    if(log.offset==0){\
      ReleaseLock(&log.log_lock);\
      break;\
    }\
    if(log.pid != getpid()||log.fd==-1){\
      close(log.fd);\
      log.pid = getpid();\
      log.fd = open_new_file(log.pid, log.thread);\
    }\
    write(log.fd, \
        (void *)&(log.buffer), \
        sizeof(recentry_t) * log.offset); \
    log.offset = 0;\
    ReleaseLock(&log.log_lock);\
  }while(0);

#define write_log(rec, log) \
  do{ \
    log.buffer[log.offset] = rec; \
    log.offset++; \
    if(!(log.offset < LOGSIZE)){ \
      if(log.pid != getpid()||log.fd==-1){\
        close(log.fd);\
        log.pid = getpid();\
        log.fd = open_new_file(log.pid, log.thread);\
      }\
      GetLock(&log.log_lock, 1);\
      write(log.fd, \
          (void *)&(log.buffer), \
          sizeof(recentry_t) * log.offset); \
      fprintf(trace, "called write, thread=%d offset=%d\n", thread_id, log.offset);\
      log.offset = 0; \
      ReleaseLock(&log.log_lock);\
    }\
  }while(0);

#define max(a,b) ((a)>(b)? (a) : (b))

void writelog_brr(uint8_t thread_id, ts_T barrtime)
{
  int i = 0;
  int k = 0;
  for(; i < (BARRNUMS + 1) / 4; i++)
  {
    recentry_t brecord;
    brecord.op = BARRIER_OP;
    brecord.thread = (uint8_t) thread_id;
    brecord.mid = 0;
    brecord.info.barrier.ts0 = barrtime[k++];
    brecord.info.barrier.ts1 = barrtime[k++];
    brecord.info.barrier.ts2 = barrtime[k++];
    brecord.info.barrier.ts3 = barrtime[k++];
    if(thread_id < MAXTHREADS) {
      write_log(brecord, logs[thread_id]);
    }
  }
  ASSERTX(k == (BARRNUMS + 1)); //you should specify barrnums as 4-multiple-minus-1
}




/*-----^^^utility function finish^^^-----------*/
uint32_t write_addr[MAXTHREADS];
string from_reg[MAXTHREADS];
uint32_t read_addr[MAXTHREADS];
string to_reg[MAXTHREADS];

bool do_tracing = false; //when it is false, we do NOTHING!!
uint32_t start_inst; //instruction that will triger start
//the 1st instruction with that ip will trigger
uint32_t stop_inst; //stop instruction that will triger the end
//no way to restart!!


//The analysis function before every memory write
VOID RecordMemWriteAddr(VOID * addr, INT32 thread_id)
{
#ifndef PERF
  assert(thread_id<MAXTHREADS);
#endif
  write_addr[thread_id] = (uint32_t)addr;
}

//The analysis function before every memory read
VOID RecordMemReadAddr(VOID * addr, INT32 thread_id)
{
#ifndef PERF
  assert(thread_id<MAXTHREADS);
#endif
  read_addr[thread_id] = (uint32_t) addr;
}


// The analysis function after every read; it prints a memory read record
VOID RecordMemRead(VOID * ip, INT32 thread_id, ADDRINT size, REG reg)
{
#ifndef PERF
  assert(thread_id < MAXTHREADS);
#endif

  if(!do_tracing) return;

  uint32_t addr;
  addr = read_addr[thread_id];
  if((unsigned int)addr > (unsigned int)STACK_LOWERBOUND) //Filter stack
    return;

  recentry_t recorded;
  recorded.info.access.addr = addr;

  // Get the program counter
  recorded.info.access.ip = (uint32_t)ip;
  // Get the destination register
  recorded.info.access.reg = reg; 
  // Record the value
  if(size > 2) {
    recorded.info.access.val = *((int *)addr);
  }
  else if(size == 2) {
    recorded.info.access.val = *((int16_t*) addr);
  }
  else if (size == 1) {
    recorded.info.access.val = *((int8_t*) addr);
  }
  else {
    return;
    //assert(false);
  }

  recorded.thread = (uint8_t)thread_id;
  recorded.op = READ_OP;
  recorded.mid = get_malloc_id(addr);
  write_log(recorded, logs[thread_id]);
}

// The analysis function after every write; it prints a memory write record
VOID RecordMemWrite(VOID * ip, INT32 thread_id, ADDRINT size, REG reg)
{
#ifndef PERF
  assert(thread_id < MAXTHREADS);
#endif
  if(!do_tracing) return;

  uint32_t addr;
  // int val;
  addr = write_addr[thread_id];

  if((unsigned int)addr > (unsigned int)STACK_LOWERBOUND) //Filter stack
    return;

  recentry_t recorded;
  recorded.info.access.addr = addr;
  recorded.info.access.ip = (uint32_t)ip;
  // Get the destination register
  recorded.info.access.reg = reg; 
  recorded.thread = (uint8_t)thread_id;
  recorded.op = WRITE_OP;
  recorded.mid = get_malloc_id(addr);
  // Record the value
  if(size > 2) {
    recorded.info.access.val = *((int *)addr);
  }
  else if(size == 2) {
    recorded.info.access.val = *((int16_t *) addr);
  }
  else if (size == 1) {
    recorded.info.access.val = *((int8_t *) addr);
  }
  else {
    return;
    //assert(false);
  }

  write_log(recorded, logs[thread_id]);

  return;
}

// Start tracing
VOID trace_start()
{
  do_tracing = true;
  cerr<<"Begin tracing"<<endl;
}

// Stop tracing
VOID trace_stop()
{
  do_tracing = false; 
  //Flush dangling output
  for(int i = 0; i<MAXTHREADS; i++){
    flush_log(logs[i]);
  }
}

bool Is_ReadPtr(VOID* pc);
bool Is_WritePtr(VOID* pc);

// Is called for every instruction and instruments reads and writes
VOID Instruction(INS ins, VOID *v)
{
  //prune out the library access ...
  if(INS_Address(ins)> USER_UPPERBOUND) return; //TODO
  if(INS_Address(ins)< USER_LOWERBOUND) return; //TODO

  if(INS_Address(ins) == start_inst){
    INS_InsertPredicatedCall(
        ins, IPOINT_BEFORE, (AFUNPTR)trace_start,
        IARG_END);
  }
  if(INS_Address(ins) == stop_inst){
    INS_InsertPredicatedCall(
        ins, IPOINT_BEFORE, (AFUNPTR)trace_stop,
        IARG_END);
  }

  // Dongdong: Instrument selected functions
  // unsigned long tmpinsaddr = (unsigned long)INS_Address(ins);
  // map<unsigned long, unsigned long>::iterator ub = map_function.upper_bound(tmpinsaddr);
  // if (ub == map_function.begin())
  //   return;
  // else if ((--ub)->second < tmpinsaddr)
  //   return;

  if(INS_IsBranchOrCall(ins)){
    return;
  }

  // Instruments loads using a predicated call, i.e.
  // the call happens iff the load will be actually executed
  // (this does not matter for ia32 but arm and ipf have predicated instructions)
  if(INS_IsMemoryRead(ins))
  {
    if(Is_ReadPtr((VOID*)INS_Address(ins)))
    {
      INS_InsertPredicatedCall(ins, IPOINT_BEFORE, 
          (AFUNPTR)RecordMemReadAddr,
          IARG_MEMORYREAD_EA,
          IARG_THREAD_ID,
          IARG_END);
      INS_InsertPredicatedCall(
          ins, IPOINT_AFTER, (AFUNPTR)RecordMemRead,
          IARG_INST_PTR,
          IARG_THREAD_ID,
          IARG_MEMORYREAD_SIZE, IARG_UINT32, 
          REG(INS_OperandReg(ins, 0)), IARG_END);
    }
  }

  if(INS_IsMemoryWrite(ins))
  {
    if(Is_WritePtr((VOID*)INS_Address(ins))){
      //address should be taken before an access, because the value
      //(usually in register) may be changed after writing
      INS_InsertPredicatedCall(ins, IPOINT_BEFORE, 
          (AFUNPTR)RecordMemWriteAddr,
          IARG_MEMORYWRITE_EA,
          IARG_THREAD_ID,
          IARG_END);

      //this was put after instruction, because when we use 'counter'
      //grab counter AFTER the access has really happened is important
      INS_InsertPredicatedCall(
          ins, IPOINT_AFTER, (AFUNPTR)RecordMemWrite,
          IARG_INST_PTR,
          IARG_THREAD_ID,
          IARG_MEMORYWRITE_SIZE, IARG_UINT32, 
          REG(INS_OperandReg(ins, 1)), IARG_END);
    }
  }
  //TODO: do we need to handle instructions that both read and write?
}

/**********************************************************
 * Instrument lock, unlock, (thread) creat, join routines**
 * *******************************************************/
VOID lock(UINT32 l, UINT32 thread_id, string* name)
{
  assert(thread_id < MAXTHREADS);

  // Prune out the library locks ...
  if(l > USER_UPPERBOUND) return; //TODO
  if(l < USER_LOWERBOUND) return; //TODO

  if(!do_tracing) return;

  //update this lock's dynamic instance
  recentry_t recorded;
  recorded.op = LOCK_OP;
  recorded.thread=(uint8_t)thread_id;
  recorded.info.lock.lock= l;
  recorded.mid = 0;

  //update lock's instance number
  GetLock(&lockmapLock, 1); //TODO, do you want to use lock?
  //TODO, an unsolved bug here :(, see _debug.C
  map<uint32_t,int>::iterator it = lock_map.find(l); 

  if(it != lock_map.end()){
    int orig = it->second;
    it->second = orig + 1;
    recorded.info.lock.instance = orig + 1;
  }
  else{
    lock_map[l] = 1;
    recorded.info.lock.instance = 1;
  }
  ReleaseLock(&lockmapLock);

  write_log(recorded, logs[thread_id]);
}

VOID unlock(UINT32 l, UINT32 thread_id, string* name)
{
  assert(thread_id<MAXTHREADS);

  // Prune out the library locks ...
  if(l > USER_UPPERBOUND) return; //TODO
  if(l < USER_LOWERBOUND) return; //TODO

  if(!do_tracing) return;

  //update this lock's dynamic instance
  recentry_t recorded;
  recorded.op = UNLOCK_OP;
  recorded.thread=(uint8_t)thread_id;
  recorded.info.lock.lock= l;
  recorded.mid  = 0;

  //update lock's instance number
  GetLock(&lockmapLock, 1);
  map<uint32_t,int>::iterator it = lock_map.find(l);
  if(it == lock_map.end()){
    /*printf("ERROR, unlocking a lock 0x%x with no record before\n",l);*/
    recorded.info.lock.instance = 0; 
    //mean no lock, TODO: be careful about this in trace handling
  }
  else{
    recorded.info.lock.instance = it->second;    
  }
  ReleaseLock(&lockmapLock);

  write_log(recorded, logs[thread_id]);
}

/*
 * The local timestamp ticks whenever there is a barrier, create, join, exit
 */
VOID barrier_entry(UINT32 b, UINT32 p, UINT32 thread_id)
{
  assert(thread_id < MAXTHREADS);
  assert(thread_id <= BARRNUMS);
  if(!do_tracing) return;

  //I need 'P' information to update barrier's progress

  thread_ts[thread_id][thread_id]++;

  //In case need a new entry in barr_map
  bts_T newbts;
  bool newused = false;
  newbts.ts[0] = (uint16_t*)calloc(BARRNUMS + 1, sizeof(uint16_t));
  newbts.ts[1] = (uint16_t*)calloc(BARRNUMS + 1, sizeof(uint16_t));
  arr2ts(thread_ts[thread_id], newbts.ts[0]);

  map<uint32_t,bts_T>::iterator it;
  GetLock(&barrLock, 1);
  it = barr_map.find(b);
  if(it != barr_map.end())
  {
    int prog = it->second.prog;
    int ongo = it->second.ongoing;
    ts_T origts = it->second.ts[ongo];
    for(int i = 0; i <= BARRNUMS; i++)
    {
      it->second.ts[ongo][i] = max(thread_ts[thread_id][i], origts[i]);
    }

    if(prog == (uint16_t)(p - 1)) {//I'm the last one of this barrier!
      int curfinish = it->second.finish;
      it->second.ongoing = curfinish;
      it->second.finish = ongo;
      it->second.prog = 0;
    }
    else {
      it->second.prog = prog + 1;
    }
  }
  else
  {
    if(p > 1) {
      newbts.ongoing = 0; //ongoing
      newbts.finish = 1;
      newbts.prog = 1;    //I am the first one~~!
    }
    else{
      newbts.ongoing = 1;
      newbts.finish  = 0;
      newbts.prog    = 0;
    }
    barr_map[b] = newbts;
    newused = true;
  }
  ReleaseLock(&barrLock);
  if(!newused)
  {
    free(newbts.ts[0]);
    free(newbts.ts[1]);
  }
}

//Every barrier participant will log the same vector-time in its log
VOID barrier_exit (UINT32 b, UINT32 p, UINT32 thread_id)
{
  assert(thread_id<MAXTHREADS);
  if(!do_tracing) return;

  //get latest timestamp from the barr_map
  //TODO: note: there might be of some synch. problem ...
  //TODO: 0925, now my assumption is, previous bar-user and next bar-user have
  //TODO:    at least one commone guy

  map<uint32_t,bts_T>::iterator it;
  it = barr_map.find(b);
  //barrier_exit always take the finished timestamp!
  ts_T barrtime = it->second.ts[it->second.finish];

  ts2arr(barrtime, thread_ts[thread_id]);
  writelog_brr(thread_id, thread_ts[thread_id]);
}

VOID create(UINT32 thread_id, VOID * cthread_id)
{
  assert(thread_id < MAXTHREADS);
  //if(!do_tracing) return;

  ASSERTX(thread_id <= BARRNUMS);
  thread_ts[thread_id][thread_id]++;

  UINT32 newtid = *(UINT32*)cthread_id;
  uint16_t* tmparr = (uint16_t*)malloc((BARRNUMS + 1) * sizeof(uint16_t));
  for(int i = 0; i < BARRNUMS + 1; i++)
  {
    tmparr[i] = thread_ts[thread_id][i];
  }

  GetLock(&createmLock, 1);
  createMap[newtid]=tmparr; //NOTE: this cannot be replaced by thread_ts
  ReleaseLock(&createmLock);

  cout<<"[gt-create] thread "<<thread_id<<" add info about create thread"<<std::hex<<"0x"<<newtid<<endl;

  writelog_brr(thread_id,thread_ts[thread_id]);
  //NOTE 1: do not free tmparr! it is used in createMap!
  //NOTE 2: the child thread will get the SAME vec-time at the beginning of
  // its log with its parent at the creation time

  // nanosleep(&sleep_time,NULL); //TODO, we may need this to trigger splash2 bug
}

VOID join(VOID* p, UINT32 thread_id)
{
  //if(!do_tracing) return;

  assert(thread_id<MAXTHREADS);


  uint32_t cosid=*(UINT32*)p;
  cout<<"[gt-join] join thread"<<std::hex<<"0x"<<cosid
    <<" by thread "<<thread_id<<"\n";

  map<UINT32,UINT32>::iterator it; 
  it = osIdpinIdMap.find(cosid);
  if(it == osIdpinIdMap.end()){
    cout<<"[gt-join] FAIL to find pin-ID of thread"<<std::hex<<"0x"<<cosid<<"\n";
    return;
  }
  uint32_t cid = it->second;
  cout<<"[gt-join] join thread"<<cid<<" by thread "<<thread_id<<"\n";
  if(cid >= MAXTHREADS){
    return; //something is wrong
  }

  //update timestamp based on join
  thread_ts[thread_id][thread_id]++;
  thread_ts[cid][cid]++; //exit should have ++, but exit was not caught
  //so we increment here

  for(int i = 0;i < BARRNUMS + 1; i++)
  {
    thread_ts[thread_id][i] = max(thread_ts[thread_id][i], thread_ts[cid][i]);
  }

  writelog_brr(thread_id, thread_ts[thread_id]);
  //Theoretically, we should also write this into the child's, but that is
  //useless anyway
}

VOID pthself(UINT32 thread_id, ADDRINT real_tid)
{
  assert(thread_id < MAXTHREADS);
  osIdpinIdMap[real_tid] = thread_id;

  //if(!do_tracing) return;

  if(thread_init[thread_id])
    return;

  //uint16_t* tmparr = NULL;
  uint16_t* tmparr=zerots; 
  //different timing at parent and child (for fft,lu)
  std::map<UINT32, uint16_t*>::iterator it;
  GetLock(&createmLock, 1);
  it = createMap.find(real_tid);
  if(it != createMap.end())
  {
    tmparr = it->second;
    cout<<"[ct-pthelf] Thead "<<std::dec<<thread_id<<"("<<real_tid<<
      ") find its inherit "<<endl;
  }
  else{
    cout<<"[ct-pthelf] Thead "<<thread_id<<"("<<real_tid<<
      ") not find its inherit "<<endl;
  }
  ReleaseLock(&createmLock);

  for(int i=0;i<BARRNUMS+1;i++)
  {
    thread_ts[thread_id][i] = max(thread_ts[thread_id][i], tmparr[i]);
  }

  writelog_brr(thread_id, thread_ts[thread_id]);
  thread_init[thread_id]=true; //I put it here, because I fear there
  //would be some 'order' issue, create function may be executed
  //later than this function, then some child may miss the timestamp
  //at the first try, but may get it next time
  //anyway, I make sure that you will only WRITE TO LOG once!

}


/**
 * Image is used to instrument functions
 * Right now, most instrumented functions are synchronization functions
 */
VOID Image(IMG img, VOID* v)
{
  RTN selfRtn = RTN_FindByName(img, "pthread_self");
  if(RTN_Valid(selfRtn))
  {
    fprintf(trace,"[debug] find pthread_self @%s @ Img %s!\n", 
        RTN_Name(selfRtn).c_str(),
        IMG_Name(img).c_str());
    RTN_Open(selfRtn);
    RTN_InsertCall(selfRtn, IPOINT_AFTER, (AFUNPTR)pthself, 
        IARG_THREAD_ID, IARG_G_RESULT0, 
        IARG_END);

    RTN_Close(selfRtn);
  }

  RTN lockRtn = RTN_FindByName(img, "__pthread_mutex_lock");
  //nptl/pthread_mutex_lock.c
  //__pthread_mutex_lock(mutex), pthread_mutex_t* mutex
  if(RTN_Valid(lockRtn))
  {
    fprintf(trace,"[debug] find lock @%s @ Img %s!\n", RTN_Name(lockRtn).c_str(),
        IMG_Name(img).c_str());

    RTN_Open(lockRtn);
    RTN_InsertCall(lockRtn, IPOINT_AFTER, (AFUNPTR)lock, 
        IARG_G_ARG0_CALLEE, IARG_THREAD_ID,IARG_PTR, 
        &(RTN_Name(lockRtn)), IARG_END);
    RTN_Close(lockRtn);
  }

  RTN unlockRtn = RTN_FindByName(img, "pthread_mutex_unlock");
  //nptl/pthread_mutex_unlock.c
  //__pthread_mutex_unlock(mutex), pthread_mutex_t* mutex
  if(RTN_Valid(unlockRtn))
  {
    fprintf(trace,"[debug] find unlock @ %s @Img %s!\n", RTN_Name(unlockRtn).c_str(),
        IMG_Name(img).c_str());
    RTN_Open(unlockRtn);
    RTN_InsertCall(unlockRtn, IPOINT_BEFORE, (AFUNPTR)unlock, IARG_G_ARG0_CALLEE, IARG_THREAD_ID,IARG_PTR, &(RTN_Name(unlockRtn)), IARG_END);
    RTN_Close(unlockRtn);
  }

  RTN createRtn = RTN_FindByName(img, "pthread_create@@GLIBC_2.1");
  //pthread_create@@GLIBC_2.1 call create_thread
  //refer to nptl/pthread_create.c, the 1st argument is pthread_t
  if(RTN_Valid(createRtn)){ 
    fprintf(trace,"[debug] find create@ %s @Img %s!\n", RTN_Name(createRtn).c_str(),
        IMG_Name(img).c_str());
    RTN_Open(createRtn);
    //TODO BEFORE or AFTER?
    //BEFORE is ok as for the argument, the new pthread is already calculated
    RTN_InsertCall(createRtn, IPOINT_AFTER, 
        (AFUNPTR)create, IARG_THREAD_ID, 
        IARG_G_ARG0_CALLEE,IARG_END);
    RTN_Close(createRtn);
  }

  RTN joinRtn = RTN_FindByName(img, "pthread_join");
  //pthread_join (threadid, thread_return) nptl/pthread_join.c
  //the first argument is pthread_t type
  if(RTN_Valid(joinRtn))
  {
    RTN_Open(joinRtn);
    //should be AFTER instead of BEFORE
    RTN_InsertCall(joinRtn, IPOINT_AFTER, (AFUNPTR)join, IARG_G_ARG0_CALLEE, IARG_THREAD_ID, IARG_END);
    RTN_Close(joinRtn);
  }

  RTN barinRtn = RTN_FindByName(img, "shan_barrier_entry");
  //in shan.h, shan_barrier_entry(void* barr)
  if(RTN_Valid(barinRtn))
  {
    RTN_Open(barinRtn);
    RTN_InsertCall(barinRtn, IPOINT_AFTER, (AFUNPTR)barrier_entry, 
        IARG_G_ARG0_CALLEE, IARG_G_ARG1_CALLEE, IARG_THREAD_ID,IARG_END);
    RTN_Close(barinRtn);
  }

  RTN baroutRtn = RTN_FindByName(img, "shan_barrier_exit");
  //in shan.h, shan_barrier_exit(void* barr)
  if(RTN_Valid(baroutRtn))
  {
    RTN_Open(baroutRtn);
    RTN_InsertCall(baroutRtn, IPOINT_BEFORE, (AFUNPTR)barrier_exit, 
        IARG_G_ARG0_CALLEE, IARG_G_ARG1_CALLEE, IARG_THREAD_ID,IARG_END);
    RTN_Close(baroutRtn);
  }
  Pin_Malloc_Id::Image_Load(img, v);
}


/**
 * The Fini is called when the instrumentation is finished. This routine flushes all the logs.
 */
VOID Fini(INT32 code, VOID *v)
{
  if(do_tracing){
    //Flush dangling output
    for(int i = 0; i<MAXTHREADS; i++){
      flush_log(logs[i]);
    }
    fprintf(trace, "#eof\n");
  }
}

/**
 * initialize the interested PCs to track
 * by default, the lists are empty
 */
map<uint32_t,bool> writePC; //set of write instructions to trace
map<uint32_t,bool> readPC;  //set of read instructions to trace

void gt_init_rwPC(int argc, char** argv)
{
  string rpcfile;
  string wpcfile;
  FILE* rf;
  FILE* wf;
  GetArg(argc, argv, "-rpc", rpcfile,"/tmp/rpc.in");
  GetArg(argc, argv, "-wpc", wpcfile,"/tmp/wpc.in");

  readPC.clear();
  writePC.clear();

  rf=fopen(rpcfile.c_str(),"r+");
  if(!rf){
    fprintf(trace,"[Warning] read-pointer pc file %s does not exist\n",rpcfile.c_str());
  }else{
    uint32_t tmp;
    while(!feof(rf)){
      fscanf(rf,"%x\n",&tmp);
      readPC[tmp]=true;
    }
  }

  wf=fopen(wpcfile.c_str(),"r+");
  if(!wf){
    fprintf(trace,"[Warning] write-pointer pc file %s does not exist\n",wpcfile.c_str());
  }else{
    uint32_t tmp;
    while(!feof(wf)){
      fscanf(wf,"%x\n",&tmp);
      writePC[tmp]=true;
    }
  }
}


/**
 * initialization function
 * step1: register all the signal handlers
 * step2: 
 */
void init(int argc,char** argv)
{

  //file preparation, thread**-**.out would be the profiling log
  getcwd(work_dir, 1000);
  trace = fopen(KnobOutputFile.Value().c_str(), "w");
  if(!trace){
    fprintf(stderr,"cannot open trace file %s\n",
        KnobOutputFile.Value().c_str());
    exit(1);
  }

  int pid=getpid();
  for(int i = 0; i < MAXTHREADS; i++){
    InitLock(&(logs[i].log_lock));
    logs[i].offset = 0;
    logs[i].fd = -1;
    logs[i].thread = i;
    logs[i].pid = pid;
  }

  //initialize data structures
  InitLock(&barrLock);
  InitLock(&lockmapLock);
  createMap.clear();

  for(int i = 0; i < MAXTHREADS; i++){
    for(int j = 0; j <= BARRNUMS; j++){
      thread_ts[i][j] = 0;
    }
    thread_init[i] = false;
  }
  for(int i = 0; i < (BARRNUMS + 1); i++){
    zerots[i] = 0;
  }

  //initialize flag, take command line input
  /* -startin, -stopin, -sig, -rpc, -wpc*/
  do_tracing = false; //waiting for signal or others
  //to start the tracing
  GetArg_ul(argc, argv, "-startin",start_inst,0,1);
  //80f24c8 for mysql4-install
  GetArg_ul(argc, argv, "-stopin" ,stop_inst ,0,1);
  //GetArg_ul(argc, argv, "-sig", use_sig,0,1);

  if(!start_inst && !stop_inst)
  {
    do_tracing = true;

  }

  gt_init_rwPC(argc, argv);

  // two choices: 1. trace from beginning to the end;
  // 2. only use instruction to trigger

  Pin_Malloc_Id::my_init();

  // Dongdong for partial instrumentation
  // Read function address file
  // ifstream funcaddr;
  // funcaddr.open(KnobFunctionFile.Value().c_str(), ios::in);
  // Init map_function
  // string linebuf;
  // while (getline(funcaddr, linebuf).eof() == false)
  //   {
  // 	size_t pos = linebuf.find('\t', 0);
  // 	string tmpentry = linebuf.substr(0, pos);
  // 	string tmpexit = linebuf.substr(pos + 1);
  // 	stringstream ss1, ss2;
  // 	ss1 << hex << tmpentry;
  // 	ss2 << hex << tmpexit;
  // 	unsigned long entry, exit;
  // 	ss1 >> entry;
  // 	ss2 >> exit;
  // 	map_function.insert(make_pair(entry, exit));
  //   }

  //^^^^^^^^^^^^Initialization finish^^^^^^^^^^^^^^^^^
}

int main(int argc, char *argv[])
{

  PIN_InitSymbols();

  if(PIN_Init(argc,argv)){
    cerr<<"Warning: error or new parameter for PIN?"<<endl;
    //return 1;//Usage();
  }

  init(argc,argv);

  IMG_AddInstrumentFunction(Image, 0);
  INS_AddInstrumentFunction(Instruction, 0);
  PIN_AddFiniFunction(Fini, 0);

  // Never returns
  PIN_StartProgram();

  fclose(trace);
  return 0;
}



/***********
 ***cmd_line input
 **************/
bool GetArg_ul(UINT32 argc, char** argv, const char* argname, UINT32& arg, UINT32 default_val, UINT32 index) 
{ //shan add to take in 0x ...
  BOOL found = false;
  UINT32 i = 0;
  do 
  {
    string* tmp = new string(argv[i]);
    if (tmp->find(argname) != string::npos) 
    {
      ASSERTX((i + index) < argc);
      arg = strtoul(argv[i+index],NULL,0);
      found = true;
    }
    else 
    {
      i++;
    }
    delete tmp;
  } while (!found && (i < argc));
  if (!found) 
  {
    arg = default_val;
  }
  return found;
}

bool GetArg(UINT32 argc, char** argv, const char* argname, string& arg, string default_val)
{
  BOOL found = false;
  UINT32 i = 0;
  do
  {
    string* tmp = new string(argv[i]);
    if (tmp->find(argname) != string::npos)
    {
      ASSERTX((i + 1) < argc);
      arg = string(argv[i + 1]);
      found = true;
    }
    else
    {
      i++;
    }
    delete tmp;
  } while (!found && (i < argc));
  if (!found)
  {
    arg = string(default_val);
  }
  return found;
}  //add by shan to take in string argument 


/**
 * @param pc -- interested pc
 * @return if we will trace this pc 
 *by default, readPC is not specificed, thus we will trace all passed-in pc
 */
bool Is_ReadPtr(VOID* pc)
{
  //if there is no readPC list, instrument every read
  if(readPC.empty()) return true;

  if(readPC.find((uint32_t)pc) != readPC.end())
    return true;
  else
    return false;
}

/**
 * @param pc -- interested pc
 * @return if we will trace this pc 
 * by default, writePC is not specificed, thus we will trace all passed-in pc
 */
bool Is_WritePtr(VOID* pc)
{
  //if there is no writePC list, instrument every write
  if(writePC.empty()) return true;

  if(writePC.find((uint32_t)pc) != writePC.end())
    return true;
  else
    return false;
}
