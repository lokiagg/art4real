#include "Tree.h"
#include "RdmaBuffer.h"
#include "Timer.h"
#include "Node.h"

#include <algorithm>
#include <city.h>
#include <iostream>
#include <queue>
#include <utility>
#include <vector>
#include <atomic>
#include <mutex>
#include <fstream>
#include <chrono>
#include <immintrin.h>

// #define USE_CN_CACHE

// extern double kWarmRatio;
// extern uint64_t kKeySpace;
double cache_miss[MAX_APP_THREAD];
double cache_hit[MAX_APP_THREAD];
uint64_t lock_fail[MAX_APP_THREAD];
// uint64_t try_lock[MAX_APP_THREAD];
uint64_t write_handover_num[MAX_APP_THREAD];
uint64_t try_write_op[MAX_APP_THREAD];
uint64_t read_handover_num[MAX_APP_THREAD];
uint64_t try_read_op[MAX_APP_THREAD];
uint64_t read_leaf_retry[MAX_APP_THREAD];
uint64_t leaf_cache_invalid[MAX_APP_THREAD];
uint64_t try_read_leaf[MAX_APP_THREAD];
uint64_t read_node_repair[MAX_APP_THREAD];
uint64_t try_read_node[MAX_APP_THREAD];
uint64_t read_node_type[MAX_APP_THREAD][MAX_NODE_TYPE_NUM];
uint64_t latency[MAX_APP_THREAD][MAX_CORO_NUM][LATENCY_WINDOWS];
volatile bool need_stop = false;
uint64_t retry_cnt[MAX_APP_THREAD][MAX_FLAG_NUM];
uint64_t MN_iops[MAX_APP_THREAD][MEMORY_NODE_NUM];
uint64_t MN_datas[MAX_APP_THREAD][MEMORY_NODE_NUM];

int update_retry_flag[MAX_APP_THREAD];
uint64_t retry_time[MAX_APP_THREAD];
//uint64_t insert_time[MAX_APP_THREAD];

int insert_type[MAX_APP_THREAD];  // 0 1 2 3 4 5 6 7

uint64_t insert_cnt[8][MAX_APP_THREAD]; //0
uint64_t internal_empty_entry[MAX_APP_THREAD]; // 1
uint64_t internal_extend_empty_entry[MAX_APP_THREAD]; // 2
uint64_t internal_header_split[MAX_APP_THREAD];  // 3
uint64_t buffer_empty_entry[MAX_APP_THREAD]; // 4
uint64_t buffer_header_split[MAX_APP_THREAD]; // 5
uint64_t buffer_reconstruct[MAX_APP_THREAD]; // 6
uint64_t in_place_update[MAX_APP_THREAD]; // 7
uint64_t write_cnt[MAX_APP_THREAD];
uint64_t cas_cnt[MAX_APP_THREAD];



uint64_t insert_time[8][MAX_APP_THREAD];  //总时间
uint64_t search_from_cache_time[8][MAX_APP_THREAD];
uint64_t read_buffer_node_time[8][MAX_APP_THREAD];  //找cache时间 一样的分8类
uint64_t read_internal_node_time[8][MAX_APP_THREAD];  //找cache时间 一样的分8类
uint64_t read_leaves_time[8][MAX_APP_THREAD]; 
uint64_t write_time[MAX_APP_THREAD];
uint64_t cas_time[MAX_APP_THREAD];
uint64_t loop_time[MAX_APP_THREAD];
uint64_t cp_time[MAX_APP_THREAD];


uint64_t search_cnt[MAX_APP_THREAD];
uint64_t search_time[MAX_APP_THREAD];
uint64_t s_search_cache_time[MAX_APP_THREAD];
uint64_t search_read_buffer_time[MAX_APP_THREAD];
uint64_t search_read_internal_time[MAX_APP_THREAD];
uint64_t search_read_leaf_time[MAX_APP_THREAD];
uint64_t cache_ops_time[MAX_APP_THREAD];
uint64_t buffer_loop[MAX_APP_THREAD];

int depth_test[MAX_APP_THREAD];

uint64_t bufffer_from_cache_cnt[MAX_APP_THREAD];
uint64_t buffer_node_all[MAX_APP_THREAD];
double   buffer_slot[MAX_APP_THREAD];

// tbb::concurrent_unordered_map<uint64_t,int> map_buffer_cnt;
/*
uint64_t internal_empty_entry_time[MAX_APP_THREAD]; //找到内部节点空槽插入的时间
uint64_t internal_extend_empty_entry_time[MAX_APP_THREAD]; //内部节点扩展的时间
uint64_t internal_header_split_time[MAX_APP_THREAD]; //内部节点分裂的时间 
uint64_t buffer_empty_entry_time[MAX_APP_THREAD]; //插入缓冲节点空槽的时间
uint64_t buffer_header_split_time[MAX_APP_THREAD]; // 缓冲节点头部分裂时间
uint64_t buffer_reconstruct_time[MAX_APP_THREAD]; // 缓冲节点重建时间
uint64_t in_place_update_time[MAX_APP_THREAD]; //就地更新时间
*/

uint64_t buffer_empty_loop_cnt[MAX_APP_THREAD];
uint64_t buffer_empty_loop_time[MAX_APP_THREAD];
uint64_t search_cache_cnt[MAX_APP_THREAD];
uint64_t read_internal_node_cnt[MAX_APP_THREAD];
uint64_t read_buffer_node_cnt[MAX_APP_THREAD];
uint64_t internal_slot_loop_cnt[MAX_APP_THREAD];
uint64_t internal_slot_loop_time[MAX_APP_THREAD];
uint64_t dur[MAX_APP_THREAD];
uint64_t cp_buffer_time[MAX_APP_THREAD];

thread_local CoroCall Tree::worker[MAX_CORO_NUM];
thread_local CoroCall Tree::master;
thread_local CoroQueue Tree::busy_waiting_queue;
thread_local GlobalAddress leaf_addrs[MAX_CORO_NUM][32];
thread_local GlobalAddress leaves_ptr[MAX_CORO_NUM][32];


std::atomic<int> cnt = 0;
std::atomic<int> search_cnt_at = 0;

uint64_t buffer_node_cnt[MAX_APP_THREAD];
uint64_t internal_node_cnt[MAX_APP_THREAD][MAX_NODE_TYPE_NUM];
uint64_t read_buffer_node_type_cnt[MAX_APP_THREAD];
uint64_t read_internal_node_type_cnt[MAX_APP_THREAD][MAX_NODE_TYPE_NUM];
uint64_t var_time[MAX_APP_THREAD];  
uint64_t search_buffer_cache_true[MAX_APP_THREAD];

double buffer_empty_slot[MAX_APP_THREAD];
uint64_t buffer_cnt_all[MAX_APP_THREAD];





Tree::Tree(DSM *dsm, uint16_t tree_id) : dsm(dsm), tree_id(tree_id) {

  assert(dsm->is_register());

// #ifdef TREE_ENABLE_CACHE
  // init local cache
// #ifdef CACHE_ENABLE_ART
  index_cache = new RadixCache(define::kIndexCacheSize, dsm);
// #else
  // index_cache = new NormalCache(define::kIndexCacheSize, dsm);
// #endif
// #endif

  local_lock_table = new LocalLockTable();

  root_ptr_ptr = get_root_ptr_ptr();

  // init root entry to Null
  auto entry_buffer = (dsm->get_rbuf(0)).get_entry_buffer();
  dsm->read_sync((char *)entry_buffer, root_ptr_ptr, sizeof(InternalEntry));
  auto root_ptr = *(InternalEntry *)entry_buffer;
  if (dsm->getMyNodeID() == 0 && root_ptr != InternalEntry::Null()) {
    auto cas_buffer = (dsm->get_rbuf(0)).get_cas_buffer();
retry:
    bool res = dsm->cas_sync(root_ptr_ptr, (uint64_t)root_ptr, (uint64_t)InternalEntry::Null(), cas_buffer);
    if (!res && (root_ptr = *(InternalEntry *)cas_buffer) != InternalEntry::Null()) {
      goto retry;
    }
  }
}
/*
void Tree::clear_cache() {
  index_cache->clear();
}
*/
GlobalAddress Tree::get_root_ptr_ptr() {
  GlobalAddress addr;
  addr.nodeID = 0;
  addr.offset = define::kRootPointerStoreOffest + sizeof(GlobalAddress) * tree_id;
  return addr;
}

InternalEntry Tree::get_root_ptr(CoroContext *cxt, int coro_id) {
  auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
  dsm->read_sync((char *)entry_buffer, root_ptr_ptr, sizeof(InternalEntry), cxt);
  return *(InternalEntry *)entry_buffer;
}

void Tree::insert(const Key &k, Value v, CoroContext *cxt, int coro_id, bool is_update, bool is_load) {
#ifdef TEST_TIME
  auto start1 = std::chrono::high_resolution_clock::now();


  auto start = std::chrono::high_resolution_clock::now();
#endif

#ifdef TEST_TIME
  auto var_time_start = std::chrono::high_resolution_clock::now();
#endif

  assert(dsm->is_register());
  int leaf_type=-1;
  int leaf_size =0;
  int klen=128,vlen=1024;   //应该从后往前找！
  uint64_t search_from_cache_time_this = 0;
  uint64_t read_buffer_node_time_this = 0;  
  uint64_t read_internal_node_time_this = 0; 
  uint64_t read_leaves_time_this = 0; 
  // traversal
  GlobalAddress p_ptr;
  InternalEntry p;
  BufferEntry bp;
  GlobalAddress node_ptr;  // node address(excluding header)
  int depth;
  int level = 1;
  int retry_flag = FIRST_TRY;
//  uint32_t fp = generateFingerprint(k);

  // cache
  bool from_cache = false;
  CacheEntry** entry_ptr_ptr = nullptr;
  CacheEntry* entry_ptr = nullptr;
  CacheEntry** cache_entry_parent_ptr = nullptr;
  CacheEntry* cache_entry_parent = nullptr;  //始终指向父节点的cache
  CacheEntry** cache_entry_buffer_ptr = nullptr;  //指向最后一层的缓冲节点
  CacheEntry* cache_entry_buffer = nullptr;
  int entry_idx = -1;//表示下层节点 特别是buffer在上层父节点的的位置
  int buffer_entry_idx = -1;//表示下层节点 特别是buffer在上层父节点的的位置
  int cache_depth = 0;
  std::vector<InternalEntry> buffer_slot;

  // temp
  GlobalAddress leaf_addr = GlobalAddress::Null();
  char* page_buffer;
  bool is_valid, type_correct;
  InternalPage* p_node = nullptr;
  InternalBuffer* bp_node = nullptr;
  InternalBuffer buffer_node;
  Header hdr;
  BufferHeader bhdr;
  int max_num;
  uint64_t* cas_buffer;
  int debug_cnt = 0;
  int parent_type = 0; //0 ->internal 1->buffer
  int parent_parent_type = -1;
  bool buffer_from_cache_flag = 0;
  int first_buffer = 0;
  // InternalPage* parent_page = nullptr;
  GlobalAddress parent_page_ptr;
  bool parent_add_to_cache_flag = false;
  bool buffer_type_change = false;
  bool buffer_initialized = false;
  Key path;
  InternalPage parent_page;
  int cnt_res=cnt.fetch_add(1);
  bool buffer_to_in = false;



  InternalBuffer parent_buffer;
  insert_cnt[0][dsm->getMyThreadID()] ++ ;
//  loop_time[dsm->getMyThreadID()] = 0;

  //search from cache
  search_cache_cnt[dsm->getMyThreadID()] ++;
#ifdef TEST_TIME
  auto var_time_stop = std::chrono::high_resolution_clock::now();
  auto var_time_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(var_time_stop - var_time_start);
  var_time[dsm->getMyThreadID()] += var_time_duration.count();
#endif


#ifdef TEST_TIME
  auto search_from_cache_start = std::chrono::high_resolution_clock::now();
#endif

#ifdef USE_CN_CACHE
  from_cache = index_cache->search_from_cache(k, entry_ptr_ptr, entry_ptr, parent_parent_type,entry_idx,buffer_entry_idx,cache_entry_parent_ptr,cache_entry_parent,first_buffer);   //check   直接从cache里面找到一个  在cache里面找到buffer直接去定位空槽的位置呗
#ifdef TEST_TIME
  auto search_from_cache_stop = std::chrono::high_resolution_clock::now();
  auto search_from_cache_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(search_from_cache_stop - search_from_cache_start);  
  search_from_cache_time[0][dsm->getMyThreadID()] += search_from_cache_duration.count();
    search_from_cache_time_this += search_from_cache_duration.count();
#endif

  if (from_cache) { // cache hit

    p_ptr = GADD(entry_ptr->addr, sizeof(InternalEntry) * entry_idx);
    p = entry_ptr->records[entry_idx];
    node_ptr = entry_ptr->addr;
    depth = entry_ptr->depth;
   // cache_depth = depth;
    parent_type  = entry_ptr->node_type;
    if(entry_ptr->node_type == 1)   //如果cache找到的缓冲节点则直接去读吧！！！  后面如果是从cache来的 并且类型就是一个缓冲节点就不用再读一遍了 还是再读一次吧、、、
    {
      cache_entry_buffer = entry_ptr;
      cache_entry_buffer_ptr = entry_ptr_ptr; 
      // depth = entry_ptr->depth;
      if(first_buffer)   //是第一个buffer 也就是位于第二层的buffer 并且这个buffer前面会有一个内部节点 这个时候cache就没有内部节点 所以没办法去失效
      {
        p_ptr = root_ptr_ptr;
        p = get_root_ptr(cxt, coro_id);
        parent_type = 0;
        depth = 1;
      }
      else{
        p_ptr = GADD(cache_entry_parent->addr,sizeof(InternalEntry)*entry_idx);
        p = cache_entry_parent->records[entry_idx];
        parent_type = cache_entry_parent->node_type;
        node_ptr = cache_entry_parent->addr;
        cache_entry_buffer = entry_ptr;
        cache_entry_buffer_ptr = entry_ptr_ptr; 
        depth =cache_entry_buffer->depth -1;
        entry_ptr = cache_entry_parent;
        entry_ptr_ptr = cache_entry_parent_ptr;
        buffer_from_cache_flag = true;
      }

    }
    else
    {
      assert(entry_idx >= 0);
      cache_entry_parent = entry_ptr;
      cache_entry_parent_ptr = entry_ptr_ptr;
      parent_page.hdr.depth = entry_ptr->depth;
    }     
    bp.val = p.val;
    if(!first_buffer) assert(cache_entry_parent !=0);  //只要是从cache拿到的一定会拿到一个父节点  不见得不见得 如果是深度为2的buffer
  }
  else {
#endif
    p_ptr = root_ptr_ptr;
    p = get_root_ptr(cxt, coro_id);
    depth = 0;
#ifdef USE_CN_CACHE
  }
#endif
  if(buffer_from_cache_flag) bufffer_from_cache_cnt[dsm->getMyThreadID()] ++;

  path[depth] = p.partial;
  depth ++;  
  cache_depth = depth; 

  UNUSED(is_update);  // is_update is only used in ROWEX_ART baseline
// if(buffer_from_cache_flag)
// {
//   for(int i =0;i<cache_entry_buffer->records.size();i++)
//   {
//     assert(cache_entry_buffer->records[i] != InternalEntry::Null());
//   }
// }
  int retry_read_buffer = 0;
next:
  retry_cnt[dsm->getMyThreadID()][retry_flag] ++;
if(parent_type ==0)  //一个内部节点    1.继续往下找  2. 有一个空槽 生成新的缓冲节点 3.内部节点分裂 分裂之后生成新的缓冲节点 4.内部节点满了扩展  并生成新的缓冲节点  
{
  if (p == InternalEntry::Null()) {  //只有可能是根节点
    assert(from_cache == false);
    auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    //新建一个缓冲节点 和叶节点 一起写过去 最后cas
    bool res = out_of_place_write_buffer_n_leaf(k,v,depth,leaf_addr,leaf_type,klen,vlen,p_ptr,p,node_ptr, cas_buffer,cxt,coro_id); //partial key正确

    // cas fail, retry
    if (!res) {   //只会发生一次 所以一定会成功匹配上
      update_retry_flag[dsm->getMyThreadID()]=1;
      retry_flag = CAS_NULL;
      p = *(InternalEntry*) cas_buffer;
      goto next;
    }
    internal_empty_entry[dsm->getMyThreadID()] ++;
    insert_type[dsm->getMyThreadID()] = 1;
    buffer_node_cnt[dsm->getMyThreadID()] ++;
    goto insert_finish;
  }
  if(p.child_type == 1)   //找buffer node 看有没有空的
  {

    bool is_match;
    auto buffer_buffer =  (dsm->get_rbuf(coro_id)).get_buffer_buffer();
    GlobalAddress addr = p.addr();
     if(buffer_from_cache_flag && from_cache && !buffer_initialized)
     {
      buffer_slot = cache_entry_buffer->records;
      bp_node = &buffer_node;
      bp_node->hdr.depth = depth;
      bp_node->rev_ptr = p_ptr;
     }
     else
{
        bp_node = &buffer_node;
      bp_node->hdr.depth = depth;
      bp_node->rev_ptr = p_ptr;
/*
      // read_buffer_node_cnt[dsm->getMyThreadID()] ++;
#ifdef TEST_TIME
      auto read_buffer_node_start = std::chrono::high_resolution_clock::now();
#endif
      is_valid = read_buffer_node(addr, buffer_buffer, p_ptr, depth, from_cache,cxt, coro_id);   
#ifdef TEST_TIME

      auto read_buffer_node_stop = std::chrono::high_resolution_clock::now();
      auto read_buffer_node_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(read_buffer_node_stop - read_buffer_node_start);  
      read_buffer_node_time[0][dsm->getMyThreadID()] += read_buffer_node_duration.count();  
      read_buffer_node_time_this += read_buffer_node_duration.count();  
#endif
      bp_node = (InternalBuffer *)buffer_buffer;
      // auto& records = bp_node->records;
      if (!is_valid) {  // node deleted || outdated cache entry in cached node
#ifdef USE_CN_CACHE
        if (buffer_from_cache_flag) {
          // index_cache->invalidate(entry_ptr_ptr, entry_ptr); //invalid 父节点 失效了有必要去失效父节点吗 没必要失效父节点  只需要更改 父节点的某个槽就行啦
          index_cache->invalidate(cache_entry_buffer_ptr, cache_entry_buffer); //invalid 缓冲节点
        }
#endif
        // re-read node entry
        auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
        dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
        InternalEntry old_p = p;
        p = *(InternalEntry *)entry_buffer;
        //把这个新的p的内容写回到父节点  
        // if(entry_idx!= -1) 
        // cache_entry_parent->records[entry_idx] = p; //  __sync_bool_compare_and_swap(&(cache_entry_parent->records[entry_idx]), old_p.val,p.val);  //新加  有可能新加的那个父节点正好是第一层的 所以不会加进去  
        from_cache = false;
        retry_flag = INVALID_Buffer_NODE;
        goto next;
      }*/
    }
  bhdr=bp_node->hdr;
  int add_to_cache_res = -1;
if(!buffer_from_cache_flag)  //buffer不是从cache来的 
{
    int flag1 = 0;
#ifdef USE_CN_CACHE
    if (depth == bhdr.depth && !buffer_from_cache_flag) {   //疯狂加入cache cache会炸掉 加还是得加
    //  printf("thread  %d 3 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)bp_node->hdr);
      // add_to_cache_res = index_cache->add_to_cache_new(k, 1,(InternalPage *)bp_node, GADD(p.addr(), sizeof(GlobalAddress) + sizeof(BufferHeader)),cache_entry_buffer,cache_entry_buffer_ptr); //加buffer到cache
    //  if(depth >1)assert(cache_entry_buffer->depth <7);
     flag1 =1;
    }
#endif

    for (int i = 0; i < bhdr.partial_len; ++ i) {    //缓冲节点分裂   新建一个共同前缀的内部节点
    if (get_partial(k, bhdr.depth + i) != bhdr.partial[i]) {     //
      //3.2 partial key not match, need split
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
      int partial_len = bhdr.depth + i - depth;  // hdr.depth may be outdated, so use partial_len wrt. depth
      bool res = out_of_place_write_node(k, v, depth, leaf_addr, leaf_type,  klen,vlen,partial_len,bhdr.partial[i], p_ptr, p, node_ptr, cas_buffer, cxt, coro_id);   //partial key正确
      if (!res) {  //失败的话一定是对同一个缓冲节点做分裂
        p = *(InternalEntry*) cas_buffer;
        from_cache = false;
        retry_flag = SPLIT_Buffer_HEADER;
        goto next;
      }
      if (from_cache) {
        index_cache->invalidate(entry_ptr_ptr, entry_ptr);
      }
      // udpate cas header. Optimization: no need to snyc; mask node_type
      auto header_buffer = (dsm->get_rbuf(coro_id)).get_header_buffer();
      auto new_hdr = BufferHeader::split_header(bhdr, i);

      bool res_d = dsm->cas_sync(GADD(p.addr(), sizeof(GlobalAddress)), (uint64_t)bhdr, (uint64_t)new_hdr, header_buffer, cxt);
      buffer_header_split[dsm->getMyThreadID()] ++;
            insert_type[dsm->getMyThreadID()] =5;
      goto insert_finish;
    }
    }
    assert(bhdr.depth !=0);

}
    depth = bhdr.depth + bhdr.partial_len;
    auto partial = get_partial(k, depth);  //获取需要匹配的关键字 应该是缓冲节点的深度再加上partial len
    //3.4 still have empty slot  不存在部分键相同的情况  有的话 则往下找 否则放空位 
  //  if(bhdr.count_1+bhdr.count_2 < 256)
   // {
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();

      GlobalAddress be_ptr;
      BufferEntry old_be;
      BufferEntry old_old_be;
     // uint8_t partial;

//      if(get_partial(k, bhdr.depth + bhdr.partial_len-1) == bhdr.partial[bhdr.partial_len-1])
//      {
#ifdef TEST_TIME
  auto stop1 = std::chrono::high_resolution_clock::now();
    auto duration_1 = std::chrono::duration_cast<std::chrono::nanoseconds>(stop1 - start1);
    dur[dsm->getMyThreadID()] += duration_1.count();
  auto buffer_empty_loop_start = std::chrono::high_resolution_clock::now();
#endif
        int start_idx = 0;
        if(buffer_from_cache_flag && buffer_entry_idx!= -1) start_idx = buffer_entry_idx;

        // 不知道是不是对的
        // start_idx = map_buffer_cnt[p.addr().val];
        // TODO: CAS 的同时把 value 写进去，，写完之后 cas 槽
faa_counter:
        start_idx = faa_buffer_counter_n_write_leaf(k,v,depth,leaf_addr,leaf_type ,klen,vlen,be_ptr,p.addr(),cas_buffer,cxt,coro_id);
        //当start_idx为0的时候就代表已经是256了
        for(int i= start_idx;i < 256 && i !=0 ;i++)  //等于256的时候 已经加1了
        {
#ifdef TEST_TIME
           auto cp_start = std::chrono::high_resolution_clock::now();
#endif
          BufferEntry b_e;
          if(buffer_from_cache_flag){
            // bp_node->records[i].val = cache_entry_buffer->records[i].val;
            bp_node->records[i].val = buffer_slot[i].val;
          }
          // b_e.val = bp_node->records[i].val;  不读buffer
#ifdef TEST_TIME
           auto cp_stop = std::chrono::high_resolution_clock::now();
     auto cp_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(cp_stop - cp_start);
           cp_time[dsm->getMyThreadID()] +=cp_duration.count();
#endif
          // if(b_e == BufferEntry::Null()) //If we are at a  buffer  empty and partial key match 不读buffer
          {
           depth ++;
          //  old_be = b_e; 不读buffer
          old_be = BufferEntry::Null();
          //  old_old_be = old_be;
           be_ptr=GADD(p.addr(), sizeof(GlobalAddress) + i * sizeof(BufferEntry));
           auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
           bool res = out_of_place_write_leaf(k,v,depth,leaf_addr,leaf_type ,klen,vlen,be_ptr,old_be,cas_buffer,cxt,coro_id);  //直接写空槽

          //  if(buffer_from_cache_flag && res && from_cache)
          //  {
              // auto new_e = BufferEntry(0,get_partial(k,depth-1),1,leaf_type,leaf_addr); 
            // cache_entry_buffer->records[i].val = new_e.val;
          //  }

           if(res) //如果说他成功了 那么本地的cache的槽应该只有这一个线程来修改吧
           {
            buffer_empty_entry[dsm->getMyThreadID()] ++;
                  insert_type[dsm->getMyThreadID()]=4;
                  depth --;
                  // buffer_node_cnt[dsm->getMyThreadID()] ++;
            
#ifdef USE_CN_CACHE   //也有可能在中间的时候就被失效了啊 这咋办？
             //加buffer到cache if(bp_node->hdr.depth >1) cache_entry_buffer->records[i].val = old_be.val;   //并且没有被失效 这个时候再加  怎么标识这个buffer有没有失效呢？？？ 直接找到他的指针吧？ 
            // bp_node->records[i].val = old_be.val;
            // index_cache->invalidate(cache_entry_buffer_ptr, cache_entry_buffer);
            // index_cache->add_to_cache(k, 1,(InternalPage *)bp_node, GADD(p.addr(), sizeof(GlobalAddress) + sizeof(BufferHeader)));
            
#endif
            // if(buffer_from_cache_flag) index_cache->invalidate(cache_entry_buffer_ptr, cache_entry_buffer);
            // index_cache->add_to_cache(k,1,(InternalPage*)bp_node,GADD(p.addr(),sizeof(GlobalAddress)+sizeof(BufferHeader)));
#ifdef TEST_TIME
              auto buffer_empty_loop_stop = std::chrono::high_resolution_clock::now();
  auto buffer_empty_loop_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(buffer_empty_loop_stop - buffer_empty_loop_start);  
            buffer_empty_loop_cnt[dsm->getMyThreadID()] ++;
            buffer_empty_loop_time[dsm->getMyThreadID()] +=buffer_empty_loop_duration.count();
#endif            
            goto insert_finish;
           }
           else {
            // auto buffer_buffer1 =  (dsm->get_rbuf(coro_id)).get_buffer_buffer();
            // read_buffer_node(p.addr(), buffer_buffer1, p_ptr, depth, buffer_from_cache_flag,cxt, coro_id);
            auto e = *(BufferEntry*) cas_buffer;  //当插入空槽失败的话 直接插下一个空槽就得了 不应该判断还有没有下一个捏 如果说一直往后面插都满了再分裂
            bp_node ->records[i].val = e.val;
            //如果这个buffer是从cache 里面来的 并且这个槽的数据可以直接拿到cache的buffer去  
            // if(buffer_from_cache_flag)  cache_entry_buffer->records[entry_idx].val = e.val;  //__sync_bool_compare_and_swap(&(cache_entry_buffer ->records[i]), 0,e.val) ; //新加
            if(buffer_from_cache_flag)  buffer_slot[i].val = e.val;
            retry_cnt[dsm->getMyThreadID()][CAS_Buffer_EMPTY] ++;
            depth --;
            goto faa_counter;
          }
        }
        }
        
       InternalBuffer old_buffer = *bp_node;
        InternalEntry old_p = p;
//读一下buffer node
        {
#ifdef TEST_TIME
      auto read_buffer_node_start = std::chrono::high_resolution_clock::now();
#endif
      is_valid = read_buffer_node(addr, buffer_buffer, p_ptr, depth, from_cache,cxt, coro_id);   
#ifdef TEST_TIME

      auto read_buffer_node_stop = std::chrono::high_resolution_clock::now();
      auto read_buffer_node_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(read_buffer_node_stop - read_buffer_node_start);  
      read_buffer_node_time[0][dsm->getMyThreadID()] += read_buffer_node_duration.count();  
      read_buffer_node_time_this += read_buffer_node_duration.count();  
#endif
      bp_node = (InternalBuffer *)buffer_buffer;
      // auto& records = bp_node->records;
      if (!is_valid) {  // node deleted || outdated cache entry in cached node
#ifdef USE_CN_CACHE
        if (buffer_from_cache_flag) {
          // index_cache->invalidate(entry_ptr_ptr, entry_ptr); //invalid 父节点 失效了有必要去失效父节点吗 没必要失效父节点  只需要更改 父节点的某个槽就行啦
          index_cache->invalidate(cache_entry_buffer_ptr, cache_entry_buffer); //invalid 缓冲节点
        }
#endif
        // re-read node entry
        auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
        dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
        InternalEntry old_p = p;
        p = *(InternalEntry *)entry_buffer;
        //把这个新的p的内容写回到父节点  
        // if(entry_idx!= -1) 
        // cache_entry_parent->records[entry_idx] = p; //  __sync_bool_compare_and_swap(&(cache_entry_parent->records[entry_idx]), old_p.val,p.val);  //新加  有可能新加的那个父节点正好是第一层的 所以不会加进去  
        from_cache = false;
        retry_flag = INVALID_Buffer_NODE;
        goto next;
      }
      if(!buffer_from_cache_flag && bp_node->lock_byte == 99)  
      {
        p_node = (InternalPage *)buffer_buffer;
        // from_cache = false;
        buffer_from_cache_flag = false;
        buffer_to_in = true;
        goto internal_node;
      }
        }
        // if(buffer_from_cache_flag) bp_node->records = cache_entry_buffer->records;
        bool res=out_of_place_write_buffer_node_new(k, v,depth,bp_node,leaf_type,klen,vlen,leaf_addr,cache_entry_parent_ptr,cache_entry_parent,buffer_slot,from_cache,buffer_from_cache_flag,p, p_ptr,buffer_type_change,cxt,coro_id);
        // if(!from_cache && buffer_type_change)  //先失效父节点（内部节点） 在这里失效的时候可以直接修改父节点的槽 这里的父节点没有太大必要再去找了 直接从上一层拿了父节点在cache的槽了 不管是不是在cache 现在肯定都存在cache了 新增
        // {
          // bool cache_res = index_cache->search_from_cache(k, entry_ptr_ptr, entry_ptr, parent_parent_type,entry_idx,cache_entry_parent_ptr,cache_entry_parent,first_buffer);
          // index_cache->invalidate(cache_entry_parent_ptr, cache_entry_parent);
        // }
#ifdef USE_CN_CACHE
        // 有个很大的问题，，如果用引用的话，那 invalidate 之后怎么办  这？？？  这里应该没有失效对 靠了
        if(buffer_from_cache_flag)   index_cache->invalidate(cache_entry_buffer_ptr, cache_entry_buffer); //invalid 缓冲节点
#endif        
        if (!res) {  //获取锁失败  获取锁失败可能是一个内部节点 所以p还是需要改  其实不管有没有获取到锁 父节点的槽都得修改 总之 获取到或者没获取到 父节点的槽指向的都应该是一个内部节点了

        auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
        dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);  //在这里直接重新读父节点会怎样  感觉可以直接重新读父节点 反正都要读 
        p = *(InternalEntry *)entry_buffer;
        // if(depth>1)
        // {

        
        // auto parent_page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
        // dsm->read_sync((char *)parent_page_buffer,GADD(p_ptr,-(sizeof(GlobalAddress)+sizeof(Header)+sizeof(InternalEntry)*entry_idx)), sizeof(InternalPage), cxt);  //在这里直接重新读父节点会怎样  感觉可以直接重新读父节点 反正都要读 
        // parent_page = *(InternalPage *)parent_page_buffer;
        // p = parent_page.records[entry_idx];

        // // if(entry_idx != -1) cache_entry_parent->records[entry_idx] = p;
        // if(from_cache)  // 这里为啥还要失效一次 因为没有获取到锁   在这里直接用这个新的槽换一下父节点呢？  直接重新读一下
        // {
        //    index_cache->invalidate(cache_entry_parent_ptr, cache_entry_parent);
        // }
        // assert(parent_page.hdr.depth <7);
        // index_cache->add_to_cache_new(k, 0,&parent_page, GADD(p_ptr,-(sizeof(Header)+sizeof(InternalEntry)*entry_idx)),cache_entry_parent,cache_entry_parent_ptr);
        // }
        // else{
        // auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
        // dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);  //在这里直接重新读父节点会怎样  感觉可以直接重新读父节点 反正都要读 
        // p = *(InternalEntry *)entry_buffer;
        // }
          buffer_from_cache_flag =false;
          retry_flag = Buffer_Switch_type;
          from_cache = false;
          //重新获取p
          goto next;
        }
        else{
        // if(entry_idx != -1) cache_entry_parent->records[entry_idx] = p;  // __sync_bool_compare_and_swap(&(cache_entry_parent->records[entry_idx]), old_p.val,p.val);       //成功之后想直接改  父节点是从cache来的 
        }  
        buffer_reconstruct[dsm->getMyThreadID()]++;
        insert_type[dsm->getMyThreadID()] =6;
        goto insert_finish;

 //         }
  //  }
  }
  //内部节点
  // 3. Find out a node
  // 3.1 read the node
  {
  #ifdef TEST_TIME
  read_internal_node_cnt[dsm->getMyThreadID()] ++;
  auto read_internal_node_start = std::chrono::high_resolution_clock::now();
  #endif
  
  
  parent_add_to_cache_flag = false;
  page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
  is_valid = read_node(p, type_correct, page_buffer, p_ptr, depth,from_cache,cxt, coro_id);
  buffer_to_in = false;
  
#ifdef TEST_TIME
  auto read_internal_node_stop = std::chrono::high_resolution_clock::now();
  auto read_internal_node_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(read_internal_node_stop - read_internal_node_start);  
  read_internal_node_time[0][dsm->getMyThreadID()] += read_internal_node_duration.count(); 
  read_internal_node_time_this += read_internal_node_duration.count(); 
#endif
}
  p_node = (InternalPage *)page_buffer;

  parent_page = *p_node;
  parent_page_ptr = p.addr();  //先不着急加到cache里面去   有可能会变成进行节点类型转换
  // assert(p_node->l_padding == 99 && buffer_to_in == false);


  if (!is_valid) {
    update_retry_flag[dsm->getMyThreadID()]=1;

    // invalidate the old node cache
#ifdef USE_CN_CACHE
    if (from_cache) {
        index_cache->invalidate(entry_ptr_ptr, entry_ptr);
    }
#endif
    // re-read node entry
    auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
    dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
    p = *(InternalEntry *)entry_buffer;
    from_cache = false;
    retry_flag = INVALID_Internal_NODE;
    goto next;
  }
l1:
internal_node:
  // 3.2 Check header
  hdr = p_node->hdr;
  if(buffer_to_in) assert(p_node->l_padding == 99);
#ifdef USE_CN_CACHE
  if (from_cache && !type_correct) {  // invalidate the out dated node type
      index_cache->invalidate(entry_ptr_ptr, entry_ptr);
  }
  if (depth == hdr.depth ) {
 //   printf("thread  %d 4 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)p_node->hdr);
    index_cache->add_to_cache_new(k, 0,p_node, GADD(p.addr(), sizeof(GlobalAddress)),cache_entry_parent,cache_entry_parent_ptr);
    parent_add_to_cache_flag = true;
  }
#endif
//  if(hdr.depth == 0) goto insert_finish;
  for (int i = 0; i < hdr.partial_len; ++ i) {
    if (get_partial(k, hdr.depth + i) != hdr.partial[i]) {
      // need split
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
      int partial_len = hdr.depth + i - depth;  // hdr.depth may be outdated, so use partial_len wrt. depth
      bool res = out_of_place_write_node(k, v,depth,leaf_addr,leaf_type,klen,vlen,partial_len,hdr.partial[i], p_ptr, p, node_ptr, cas_buffer, cxt, coro_id);   //内部节点分裂  分裂后往新的内部节点下申请一个新的缓冲节点和叶节点 partial key没问题

      // cas fail, retry
      if (!res) {
        update_retry_flag[dsm->getMyThreadID()]=1;
        p = *(InternalEntry*) cas_buffer;
        retry_flag = SPLIT_Internal_HEADER;
        from_cache = false;
        goto next;
      }
      // invalidate cache node due to outdated cache entry in cache node
#ifdef USE_CN_CACHE
      if (from_cache) {
        index_cache->invalidate(entry_ptr_ptr, entry_ptr);
      }
#endif
      // udpate cas header. Optimization: no need to snyc; mask node_type
      auto header_buffer = (dsm->get_rbuf(coro_id)).get_header_buffer();
      auto new_hdr = Header::split_header(hdr, i);
      bool res_1 =dsm->cas_sync(GADD(p.addr(), sizeof(GlobalAddress) + 256 * sizeof(InternalEntry)), (uint64_t)hdr, (uint64_t)new_hdr, header_buffer,cxt);
      internal_header_split[dsm->getMyThreadID()] ++;
            insert_type[dsm->getMyThreadID()] = 3;
            buffer_node_cnt[dsm->getMyThreadID()] ++;
      goto insert_finish;
    }
  }
      // assert(hdr.depth !=0);

  for(int i = depth;i<hdr.depth + hdr.partial_len;i++) path[i] = hdr.partial[i-depth];
  depth = hdr.depth + hdr.partial_len;

  node_ptr = GADD(p.addr(), sizeof(GlobalAddress));


  // 3.3 try get the next internalEntry
  // max_num = node_type_to_num(p.type());
  max_num =256;
  // search a exists slot first 难道是在内部节点里面找很耗时？？
#ifdef TEST_TIME  
  internal_slot_loop_cnt[dsm->getMyThreadID()] ++;
  auto internal_slot_loop_start = std::chrono::high_resolution_clock::now();
#endif
  int internal_start = 0;
  for (int i = 0; i < max_num; ++ i) {   //可能是节点的类型没有cas成功？
    auto old_e = p_node->records[i];
    if (old_e != InternalEntry::Null() && old_e.partial == get_partial(k, depth)) {
      p_ptr = GADD(p.addr(), sizeof(GlobalAddress) + i * sizeof(InternalEntry));
      p = old_e;
      from_cache = false;
 
      retry_flag = FIND_NEXT;
      parent_type = 0;
      // if(depth > 1) entry_idx =i;
      entry_idx =i;
      path[depth] = p.partial;
      depth ++;
      level ++;
#ifdef TEST_TIME

      auto internal_slot_loop_stop = std::chrono::high_resolution_clock::now();
auto internal_slot_loop_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(internal_slot_loop_stop - internal_slot_loop_start);
      internal_slot_loop_time[dsm->getMyThreadID()] += internal_slot_loop_duration.count();
#endif
      
      goto next;  // search next level
    }
    if(old_e == InternalEntry::Null())
    {
      internal_start = i;
      break;
    } 
  }

  // if no match slot, then find an empty slot to insert leaf directly
  for (int i = internal_start; i < max_num; ++ i) {   
    auto old_e = p_node->records[i];
    if (old_e == InternalEntry::Null()) {   
      auto e_ptr = GADD(p.addr(), sizeof(GlobalAddress) + i * sizeof(InternalEntry));
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
      bool res = out_of_place_write_buffer_n_leaf(k,v,depth +1,leaf_addr,leaf_type,klen,vlen,e_ptr,old_e,node_ptr,cas_buffer,cxt,coro_id);
      // cas success, return
      if (res) {
        internal_empty_entry[dsm->getMyThreadID()] ++;
            insert_type[dsm->getMyThreadID()] = 1;
            buffer_node_cnt[dsm->getMyThreadID()] ++;
        goto insert_finish;
      }
      else{
      auto e = *(InternalEntry*) cas_buffer;
      if (e.partial == get_partial(k, depth))
      {
      p = e;
      p_ptr = e_ptr;
      parent_type = 0;
      from_cache = false;
      retry_flag = CAS_Internal_EMPTY;
      depth++;  
      goto next;
      }
      }
    }
  }
  // 3.4 node is full, switch node type

  int slot_id;
  cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();  //可能存了一样的partial
  if (insert_behind(k, v,p.addr(), depth, leaf_addr,get_partial(k,depth), p.type(),leaf_type,klen, vlen,node_ptr,cas_buffer,slot_id,cxt,coro_id)){  // insert success
    //  auto page_buffer2 = (dsm->get_rbuf(coro_id)).get_page_buffer();
   //   read_node(p, type_correct, page_buffer2, p_ptr, depth,from_cache,cxt, coro_id);
    
    
    auto next_type = num_to_node_type(slot_id);
    cas_node_type(next_type, p_ptr, p, hdr, cxt, coro_id);
#ifdef USE_CN_CACHE
    if (from_cache) {  // cache is outdated since node type is changed
      index_cache->invalidate(entry_ptr_ptr, entry_ptr);
    }
#endif
    internal_extend_empty_entry[dsm->getMyThreadID()];
        insert_type[dsm->getMyThreadID()] = 2;
                internal_node_cnt[dsm->getMyThreadID()][p.node_type] --;
        internal_node_cnt[dsm->getMyThreadID()][(int)next_type] ++;
        buffer_node_cnt[dsm->getMyThreadID()] ++;

    // printf("internal type %d  to %d \n", (int)p.node_type,node_type_to_num(next_type) );
    goto insert_finish;
  }
  else {  // same partial keys insert to the same empty slot
    p_ptr = GADD(node_ptr, slot_id * sizeof(InternalEntry));
    p = *(InternalEntry*) cas_buffer;
    from_cache = false;
    depth ++;
    retry_flag = INSERT_BEHIND_EMPTY;
    goto next;
  }
}
else{  //一个缓冲节点 1.找到一样的叶节点了 2.插空槽 3.缓冲节点头部分裂 4.缓冲节点满了 结构化修改 

  if (bp == BufferEntry::Null()) {      //直接写 写了cas  

      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();

      //新建一个缓冲节点 和叶节点 一起写过去 最后cas

      auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
      new (leaf_buffer) Leaf_kv(p_ptr,leaf_type,klen,vlen,k, v);
      leaf_addr = dsm->alloc(sizeof(Leaf_kv));

      auto new_be = BufferEntry(0,get_partial(k,depth-1), 1,leaf_type,leaf_addr);

      dsm->write_sync(leaf_buffer, leaf_addr, sizeof(Leaf_kv), cxt);
      bool res = dsm->cas_sync(p_ptr, (uint64_t)bp, (uint64_t)new_be, cas_buffer, cxt);

      // cas fail, retry
      if (!res) {
        update_retry_flag[dsm->getMyThreadID()]=1;
        bp = *(BufferEntry*) cas_buffer;
        retry_flag = CAS_Buffer_EMPTY;
        from_cache = false;
        goto next;
      }
      buffer_empty_entry[dsm->getMyThreadID()] ++;
      insert_type[dsm->getMyThreadID()]=4;
      goto insert_finish;
    }


  if(bp.node_type == 1)   //找buffer node 看有没有空的
  {

    bool is_match;
    auto buffer_buffer =  (dsm->get_rbuf(coro_id)).get_buffer_buffer();
    GlobalAddress addr = bp.addr();
  //  if(buffer_from_cache_flag)
    {
    }
   // else
   {  retry_read_buffer ++;
      is_valid = read_buffer_node(addr, buffer_buffer, p_ptr, depth, from_cache,cxt, coro_id);   
      bp_node = (InternalBuffer *)buffer_buffer;
 //     parent_buffer =*bp_node;
          //3.1 check partial key
      if (!is_valid) {  // node deleted || outdated cache entry in cached node
        if (from_cache) {
          index_cache->invalidate(entry_ptr_ptr, entry_ptr);
        }
        // re-read node entry
        auto entry_buffer = (dsm->get_rbuf(coro_id)).get_buffer_entry_buffer();
        dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
        bp = *(BufferEntry *)entry_buffer;
        from_cache = false;
        retry_flag = INVALID_Buffer_NODE;
        goto next;
      }
    } 

    bhdr=bp_node->hdr;
#ifdef USE_CN_CACHE
    if (depth == bhdr.depth) {
    //      printf("thread  %d 5 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)bp_node->hdr);
    // index_cache->add_to_cache(k, 1,(InternalPage *)bp_node, GADD(bp.a0ddr(), sizeof(GlobalAddress) + sizeof(BufferHeader)));
    }
#endif

    for (int i = 0; i < bhdr.partial_len; ++ i) {    //缓冲节点分裂   新建一个共同前缀的内部节点
    if (get_partial(k, bhdr.depth + i) != bhdr.partial[i]) {
      //3.2 partial key not match, need split
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
      int partial_len = bhdr.depth + i - depth;  // hdr.depth may be outdated, so use partial_len wrt. depth
      bool res = out_of_place_write_node_from_buffer(k, v, depth, leaf_addr, leaf_type,  klen,vlen,partial_len,bhdr.partial[i], p_ptr, bp, node_ptr, cas_buffer, cxt, coro_id);   //缓冲节点下面的缓冲节点进行分裂
      if (!res) {
        bp = *(BufferEntry*) cas_buffer;
        retry_flag = SPLIT_Buffer_HEADER;
        from_cache = false;
        goto next;
      }
      if (from_cache) {
        index_cache->invalidate(entry_ptr_ptr, entry_ptr);
      }
      // udpate cas header. Optimization: no need to snyc; mask node_type
      auto header_buffer = (dsm->get_rbuf(coro_id)).get_header_buffer();
      auto new_hdr = BufferHeader::split_header(bhdr, i);

      bool res_d=dsm->cas_sync(GADD(bp.addr(), sizeof(GlobalAddress)), (uint64_t)bhdr, (uint64_t)new_hdr, header_buffer,cxt);
      buffer_header_split[dsm->getMyThreadID()] ++;
      insert_type[dsm->getMyThreadID()] =5;
      goto insert_finish;
    }
    }
    depth = bhdr.depth + bhdr.partial_len;
    auto partial = get_partial(k, depth);
    //3.4 still have empty slot  不存在部分键相同的情况  有的话 则往下找 否则放空位 
  //  if(bhdr.count_1+bhdr.count_2 < 256)
    //{
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();

      GlobalAddress be_ptr;
      BufferEntry old_be;
    //  uint8_t partial;
        for(int i=0;i < 256;i++)
        {
          if(bp_node->records[i] == BufferEntry::Null()||bp_node->records[i].val ==0) //If we are at a  buffer  empty and partial key match
          {
           depth ++;
           old_be = bp_node->records[i];
           be_ptr=GADD(bp.addr(), sizeof(GlobalAddress) + i * sizeof(BufferEntry));
           auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
           bool res = out_of_place_write_leaf(k,v,depth,leaf_addr,leaf_type ,klen,vlen,be_ptr,old_be,cas_buffer,cxt,coro_id);
           if(res)
           {
            buffer_empty_entry[dsm->getMyThreadID()]++;
                  insert_type[dsm->getMyThreadID()]=4;
            goto insert_finish;
           } 
           else {
            auto e = *(BufferEntry*) cas_buffer;
            if (e.partial == get_partial(k, depth)) {  // same partial keys insert to the same empty slot  再次查找本层 
              bp = e;
              from_cache = false;
              retry_flag = CAS_Buffer_EMPTY;
              goto next;  // search next level
              }
          }
        }
      }
  //有重复的 需要将重复的拿下来到下一级缓冲节点
          bool res=out_of_place_write_buffer_node_from_buffer(k, v,depth,bp_node,leaf_type,klen,vlen,leaf_addr,entry_ptr_ptr, entry_ptr,from_cache,bp, p_ptr,cxt,coro_id);

          if (!res) {
        auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
        dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(BufferEntry), cxt);
        bp = *(BufferEntry *)entry_buffer;
          //  bp = *(BufferEntry*) cas_buffer;
            retry_flag = Buffer_Switch_type;
            from_cache = false;
            goto next;
          }
          buffer_reconstruct[dsm->getMyThreadID()] ++;
                  insert_type[dsm->getMyThreadID()] =6;
          goto insert_finish;

     //     }
   // }
  }

  //内部节点
  // 3. Find out a node
  // 3.1 read the node
  page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
  is_valid = read_node_from_buffer(bp, type_correct,page_buffer,p_ptr,depth, from_cache,cxt,coro_id);
  p_node = (InternalPage *)page_buffer;
//  parent_buffer =*bp_node;
  if (!is_valid) {  // node deleted || outdated cache entry in cached node

    // invalidate the old node cache
    if (from_cache) {
        index_cache->invalidate(entry_ptr_ptr, entry_ptr);
    }
    // re-read node entry
    auto entry_buffer = (dsm->get_rbuf(coro_id)).get_buffer_entry_buffer();
    dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(BufferEntry), cxt);
    bp = *(BufferEntry *)entry_buffer;
    from_cache = false;
    retry_flag = INVALID_Internal_NODE;
    goto next;
  }
  // 3.2 Check header
  hdr = p_node->hdr;

  if (from_cache && !type_correct) {  // invalidate the out dated node type
    index_cache->invalidate(entry_ptr_ptr, entry_ptr);
  }
#ifdef USE_CN_CACHE  
  if (depth == hdr.depth) {
      //    printf("thread  %d 6 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)p_node->hdr);
    index_cache->add_to_cache(k, 0,p_node, GADD(p.addr(), sizeof(GlobalAddress)));
  }
#endif  


  for (int i = 0; i < hdr.partial_len; ++ i) {
    if (get_partial(k, hdr.depth + i) != hdr.partial[i]) {
      // need split
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
      int partial_len = hdr.depth + i - depth;  // hdr.depth may be outdated, so use partial_len wrt. depth
      bool res = out_of_place_write_node_from_buffer(k, v, depth, leaf_addr,leaf_type,klen,vlen, partial_len,hdr.partial[i], p_ptr, bp, node_ptr, cas_buffer, cxt, coro_id);   //内部节点分裂  分裂后往新的内部节点下申请一个新的缓冲节点和叶节点
      // cas fail, retry
      if (!res) {
        update_retry_flag[dsm->getMyThreadID()]=1;
        bp = *(BufferEntry*) cas_buffer;
        retry_flag = SPLIT_Internal_HEADER;
        from_cache = false;
        goto next;
      }
      // invalidate cache node due to outdated cache entry in cache node
      if (from_cache) {
        index_cache->invalidate(entry_ptr_ptr, entry_ptr);
      }

      // udpate cas header. Optimization: no need to snyc; mask node_type
      auto header_buffer = (dsm->get_rbuf(coro_id)).get_header_buffer();
      auto new_hdr = Header::split_header(hdr, i);
      dsm->cas(GADD(bp.addr(), sizeof(GlobalAddress)), (uint64_t)hdr, (uint64_t)new_hdr, header_buffer, false, cxt);
      internal_header_split[dsm->getMyThreadID()] ++;
      insert_type[dsm->getMyThreadID()] = 3;
      goto insert_finish;
    }
  }
      assert(hdr.depth !=0);
  depth = hdr.depth + hdr.partial_len;
#ifdef TREE_TEST_ROWEX_ART
  if (!is_update) unlock_node(node_ptr, cxt, coro_id);
  node_ptr = GADD(p.addr(), sizeof(GlobalAddress) );
  if (!is_update) lock_node(node_ptr, cxt, coro_id);
#else
  node_ptr = GADD(bp.addr(), sizeof(GlobalAddress) );
#endif

  // 3.3 try get the next internalEntry
  max_num = node_type_to_num(bp.type());
  // search a exists slot first
  for (int i = 0; i < max_num; ++ i) {
    auto old_e = p_node->records[i];
    if (old_e != InternalEntry::Null() && old_e.partial == get_partial(k, depth)) {
      p_ptr = GADD(bp.addr(), sizeof(GlobalAddress)+ i * sizeof(InternalEntry));
      p = old_e;
      from_cache = false;
      depth ++;
      retry_flag = FIND_NEXT;
      parent_type = 0;
      goto next;  // search next level
    }
  }
  // if no match slot, then find an empty slot to insert leaf directly
  for (int i = 0; i < max_num; ++ i) {
    auto old_e = p_node->records[i];
    if (old_e == InternalEntry::Null()) {
      auto e_ptr = GADD(bp.addr(), sizeof(GlobalAddress) + i * sizeof(InternalEntry));
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
      bool res = out_of_place_write_buffer_n_leaf(k,v,depth +1,leaf_addr,leaf_type,klen,vlen,e_ptr,old_e,node_ptr,cas_buffer,cxt,coro_id);
      // cas success, return
      if (res) {
        internal_empty_entry[dsm->getMyThreadID()] ++;
            insert_type[dsm->getMyThreadID()] = 1;
        goto insert_finish;
      }
      else{
      auto e = *(InternalEntry*) cas_buffer;
      if (e.partial == get_partial(k, depth))
      {
      p = old_e;
      p_ptr = e_ptr;
      parent_type = 0;
      from_cache = false;
      retry_flag = CAS_Internal_EMPTY;
      depth++;  
      goto next;
      }
      }
    }
  }
    // 3.4 node is full, switch node type

  int slot_id;
  cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
  if (insert_behind(k, v, bp.addr(), depth,leaf_addr,get_partial(k,depth), bp.type(),leaf_type,klen, vlen,node_ptr,cas_buffer,slot_id,cxt,coro_id)){  // insert success
    auto next_type = num_to_node_type(slot_id);
    cas_node_type_from_buffer(next_type, p_ptr, bp, hdr, cxt, coro_id);
    if (from_cache) {  // cache is outdated since node type is changed
      index_cache->invalidate(entry_ptr_ptr, entry_ptr);
    }
    internal_extend_empty_entry[dsm->getMyThreadID()] ++;
    insert_type[dsm->getMyThreadID()] = 2;
    goto insert_finish;
  }
  else {  // same partial keys insert to the same empty slot
    p_ptr = GADD(node_ptr, slot_id * sizeof(InternalEntry));
    p = *(InternalEntry*) cas_buffer;
    from_cache = false;
    depth ++;
    retry_flag = INSERT_BEHIND_EMPTY;
    goto next;
  }
}

insert_finish:
#ifdef TEST_TIME
  auto stop = std::chrono::high_resolution_clock::now();
  auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(stop - start);
  insert_time[0][dsm->getMyThreadID()] += duration.count();
  insert_time[insert_type[dsm->getMyThreadID()]][dsm->getMyThreadID()] += duration.count();
  search_from_cache_time[insert_type[dsm->getMyThreadID()]][dsm->getMyThreadID()] += search_from_cache_time_this;
  read_buffer_node_time[insert_type[dsm->getMyThreadID()]][dsm->getMyThreadID()] += read_buffer_node_time_this;
  read_internal_node_time[insert_type[dsm->getMyThreadID()]][dsm->getMyThreadID()] += read_internal_node_time_this;
  read_leaves_time[insert_type[dsm->getMyThreadID()]][dsm->getMyThreadID()] += read_leaves_time_this;
#endif
  insert_cnt[insert_type[dsm->getMyThreadID()]][dsm->getMyThreadID()] ++;
  depth_test[dsm->getMyThreadID()] = std::max(level+1,depth_test[dsm->getMyThreadID()]);
#ifdef TREE_TEST_ROWEX_ART
  if (!is_update) unlock_node(node_ptr, cxt, coro_id);
#endif
    auto hit = (cache_depth == 1 ? 0 : (double)cache_depth / depth);
    cache_hit[dsm->getMyThreadID()] += hit;
    cache_miss[dsm->getMyThreadID()] += (1 - hit);
  return;
}



bool Tree::read_leaf(GlobalAddress &leaf_addr, char *leaf_buffer, int leaf_size, const GlobalAddress &p_ptr, bool from_cache, CoroContext *cxt, int coro_id) {
  try_read_leaf[dsm->getMyThreadID()] ++;
re_read:
  dsm->read_sync(leaf_buffer, leaf_addr, leaf_size, cxt);
  auto leaf = (Leaf_kv *)leaf_buffer;
  // udpate reverse pointer if needed
  if (!from_cache && leaf->rev_ptr != p_ptr) {
    auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    dsm->cas(leaf_addr, leaf->rev_ptr, p_ptr, cas_buffer, false, cxt);
    // dsm->cas_sync(leaf_addr, leaf->rev_ptr, p_ptr, cas_buffer, cxt);
  }
  // invalidation
  if (!leaf->is_valid(p_ptr, from_cache)) {
    leaf_cache_invalid[dsm->getMyThreadID()] ++;
    return false;
  }
  if (!leaf->is_consistent()) {
    read_leaf_retry[dsm->getMyThreadID()] ++;
    goto re_read;
  }
  return true;
}

bool Tree::read_leaves(GlobalAddress* leaf_addrs, char *leaf_buffer,int leaf_cnt, GlobalAddress* p_ptr, bool from_cache,CoroContext *cxt, int coro_id) {  //read_batch  !!!问题在哪里！
  try_read_leaf[dsm->getMyThreadID()] ++;
  std::vector<RdmaOpRegion> rs;
  int retry_time = 0;
re_read:
  std::memset(leaf_buffer, 0, leaf_cnt*define::allocAlignPageSize);
  rs.clear();
    Leaf_kv * leaf;
    // 2.3.1 read the leaf
    for(int i =0;i<leaf_cnt;i++)
    {
      RdmaOpRegion r;
      memset(&r,0,sizeof(RdmaOpRegion));
      r.source     = (uint64_t)leaf_buffer + i * define::allocAlignPageSize;
      r.dest       = leaf_addrs[i];
      r.size       = sizeof(Leaf_kv);
      r.is_on_chip = false;
      rs.push_back(r);
    }
    dsm->read_batches_new_sync(rs,cxt,coro_id);

    for(int i =0;i<leaf_cnt;i++)
    {
      leaf = (Leaf_kv *)(leaf_buffer + i*define::allocAlignPageSize);
      // uint64_t kk_v =  key2int(leaf->key);
    //  printf("leaf key is %d %d\n",(int)key2int(leaf->key),cnt);
 //     printf("leaf value is %d\n",(int)key2int(leaf->value));
      if (!from_cache && leaf->rev_ptr != p_ptr[i]) {
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
      dsm->cas(leaf_addrs[i], leaf->rev_ptr, p_ptr[i], cas_buffer, false, cxt);
      // dsm->cas_sync(leaf_addr, leaf->rev_ptr, p_ptr, cas_buffer, cxt);
      }
      // invalidation
      if (!leaf->is_valid(p_ptr[i], from_cache)) {
      leaf_cache_invalid[dsm->getMyThreadID()] ++;
      return false;
      }
      if (!leaf->is_consistent()) {   //判断校验和的时候 ？？？  
      retry_time ++;
      read_leaf_retry[dsm->getMyThreadID()] ++;
      goto re_read;
      }
    }
  return true;
}

bool Tree::read_small_leaves(GlobalAddress* leaf_addrs, char *leaf_buffer,int leaf_cnt, GlobalAddress* p_ptr, bool from_cache,CoroContext *cxt, int coro_id) {  //read_batch  !!!问题在哪里！
  try_read_leaf[dsm->getMyThreadID()] ++;
  std::vector<RdmaOpRegion> rs;
  int retry_time = 0;
re_read:
  std::memset(leaf_buffer, 0, leaf_cnt*define::allocAlignPageSize);
  rs.clear();
    Leaf_kv * leaf;
    // 2.3.1 read the leaf
//    auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaves_buffer(leaf_cnt); 
    for(int i =0;i<leaf_cnt;i++)
    {
      RdmaOpRegion r;
      memset(&r,0,sizeof(RdmaOpRegion));
      r.source     = (uint64_t)leaf_buffer + i * define::allocAlignPageSize;
      r.dest       = leaf_addrs[i];
      r.size       = sizeof(Leaf_kv);
      r.is_on_chip = false;
      rs.push_back(r);
    }
    dsm->read_small_batches_sync(rs,cxt,coro_id);

    for(int i =0;i<leaf_cnt;i++)
    {
      leaf = (Leaf_kv *)(leaf_buffer + i*define::allocAlignPageSize);
      // uint64_t kk_v =  key2int(leaf->key);
    //  printf("leaf key is %d %d\n",(int)key2int(leaf->key),cnt);
 //     printf("leaf value is %d\n",(int)key2int(leaf->value));
      if (!from_cache && leaf->rev_ptr != p_ptr[i]) {
      auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
      dsm->cas(leaf_addrs[i], leaf->rev_ptr, p_ptr[i], cas_buffer, false, cxt);
      // dsm->cas_sync(leaf_addr, leaf->rev_ptr, p_ptr, cas_buffer, cxt);
      }
      // invalidation
      if (!leaf->is_valid(p_ptr[i], from_cache)) {
      leaf_cache_invalid[dsm->getMyThreadID()] ++;
      return false;
      }
      if (!leaf->is_consistent()) {   //判断校验和的时候 ？？？  
      retry_time ++;
      read_leaf_retry[dsm->getMyThreadID()] ++;
      goto re_read;
      }
    }
  return true;
}

bool Tree::out_of_place_write_buffer_n_leaf(const Key &k, Value &v, int depth, GlobalAddress& leaf_addr,int leaf_type,int klen,int vlen,const GlobalAddress &p_ptr, const InternalEntry &p, const GlobalAddress& node_addr, uint64_t *ret_buffer,CoroContext *cxt, int coro_id)
{
    GlobalAddress b_addr;
    b_addr = dsm->alloc(sizeof(InternalBuffer));   
    auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
    Leaf_kv *leaf = new (leaf_buffer) Leaf_kv(GADD(b_addr,sizeof(GlobalAddress)),leaf_type,klen,vlen,k, v);
    if(leaf_addr == GlobalAddress::Null()) leaf_addr = dsm->alloc(sizeof(Leaf_kv));
    auto b_buffer=(dsm->get_rbuf(coro_id)).get_buffer_buffer();
   // if(p.addr().val == 0)printf("0002!\n");
    InternalBuffer* buffer = new (b_buffer) InternalBuffer(k,define::bPartialLenMax,depth,1,1,p_ptr);  // 暂时定初始2B作为partial key buffer地址
   // printf("thread  %d 1 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)buffer->hdr);
    buffer->records[0] = BufferEntry(0,get_partial(k,depth+buffer->hdr.partial_len),1,leaf_type,leaf_addr);
    auto new_e = InternalEntry(get_partial(k,depth-1), 1, b_addr);
    RdmaOpRegion *rs =  new RdmaOpRegion[2];
    {
      rs[0].source     = (uint64_t)b_buffer;
      rs[0].dest       = b_addr;
      rs[0].size       = sizeof(InternalBuffer);
      rs[0].is_on_chip = false;
    }
    {
      rs[1].source     = (uint64_t)leaf_buffer;
      rs[1].dest       = leaf_addr;
      rs[1].size       = sizeof(Leaf_kv);
      rs[1].is_on_chip = false;
    }
    dsm->write_batches_sync(rs, 2, cxt, coro_id);
    bool res = dsm->cas_sync(p_ptr, (uint64_t)p, (uint64_t)new_e, ret_buffer, cxt);
#ifdef USE_CN_CACHE    
    if(res)
    {
    //  printf("thread  %d 2 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)buffer->hdr);
     //加buffer到cache index_cache->add_to_cache(k, 1,(InternalPage*)buffer, GADD(b_addr, sizeof(GlobalAddress) + sizeof(BufferHeader))); 
    }
#endif

    delete[] rs;
    return res;
}
void Tree::in_place_update_leaf(const Key &k, Value &v, const GlobalAddress &leaf_addr, int leaf_type,Leaf_kv* leaf,  
                               CoroContext *cxt, int coro_id) {
#ifdef TREE_ENABLE_EMBEDDING_LOCK
  static const uint64_t lock_cas_offset = ROUND_DOWN(STRUCT_OFFSET(Leaf_kv, lock_byte), 3);
  static const uint64_t lock_mask       = 1UL << ((STRUCT_OFFSET(Leaf_kv, lock_byte) - lock_cas_offset) * 8);
#endif

  auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();

  // lock function
  auto acquire_lock = [=](const GlobalAddress &unique_leaf_addr) {
#ifdef TREE_ENABLE_EMBEDDING_LOCK
    bool res=dsm->cas_mask_sync(GADD(unique_leaf_addr, lock_cas_offset), 0UL, ~0UL, cas_buffer, lock_mask, cxt);

    return res;
#else
    GlobalAddress lock_addr;
    uint64_t mask;
    get_on_chip_lock_addr(unique_leaf_addr, lock_addr, mask);
    bool res=dsm->cas_dm_mask_sync(lock_addr, 0UL, ~0UL, cas_buffer, mask, cxt);

    return res;
#endif
  };

  // unlock function
  auto unlock = [=](const GlobalAddress &unique_leaf_addr){
#ifdef TREE_ENABLE_EMBEDDING_LOCK
    dsm->cas_mask_sync(GADD(unique_leaf_addr, lock_cas_offset), ~0UL, 0UL, cas_buffer, lock_mask, cxt);

#else
    GlobalAddress lock_addr;
    uint64_t mask;
    get_on_chip_lock_addr(unique_leaf_addr, lock_addr, mask);
    dsm->cas_dm_mask_sync(lock_addr, ~0UL, 0UL, cas_buffer, mask, cxt);

#endif
  };

  // start lock & write & unlock
  bool lock_handover = false;
#ifdef TREE_TEST_HOCL_HANDOVER
#ifdef TREE_ENABLE_EMBEDDING_LOCK
  // write w/o unlock
  auto write_without_unlock = [=](const GlobalAddress &unique_leaf_addr){
    dsm->write_sync((const char*)leaf, unique_leaf_addr, sizeof(Leaf_kv), cxt);

  };
  // write and unlock
  auto write_and_unlock = [=](const GlobalAddress &unique_leaf_addr){
    leaf->unlock();
    dsm->write_sync((const char*)leaf, unique_leaf_addr, sizeof(Leaf_kv), cxt);

  };
#endif

  lock_handover = local_lock_table->acquire_local_lock(leaf_addr, &busy_waiting_queue, cxt, coro_id);
#endif
  if (lock_handover) {
    goto write_leaf;
  }
  // try_lock[dsm->getMyThreadID()] ++;

re_acquire:
  if (!acquire_lock(leaf_addr)){
    if (cxt != nullptr) {
      busy_waiting_queue.push(std::make_pair(coro_id, [](){ return true; }));
      (*cxt->yield)(*cxt->master);
    }
    lock_fail[dsm->getMyThreadID()] ++;
    update_retry_flag[dsm->getMyThreadID()]=1;
    goto re_acquire;
  }

write_leaf:
#ifdef TREE_TEST_HOCL_HANDOVER
  // in-place write leaf & unlock
  assert(leaf->get_key() == k);
  leaf->set_value(v);
  leaf->set_consistent();
  leaf->leaf_type = leaf_type;
#ifdef TREE_ENABLE_EMBEDDING_LOCK
  // write back the lock at the same time
  local_lock_table->release_local_lock(leaf_addr, unlock, write_without_unlock, write_and_unlock);
#else
  dsm->write_sync((const char*)leaf, leaf_addr, sizeof(Leaf_kv), cxt);
  local_lock_table->release_local_lock(leaf_addr, unlock);
#endif

#else
  UNUSED(unlock);
  // in-place write leaf & unlock
  assert(leaf->get_key() == k);
#ifdef TREE_ENABLE_WRITE_COMBINING
  local_lock_table->get_combining_value(k, v);
#endif
  leaf->set_value(v);
  leaf->set_consistent();
  leaf->leaf_type = leaf_type;
#ifdef TREE_ENABLE_EMBEDDING_LOCK
  // write back the lock at the same time
  leaf->unlock();
  dsm->write_sync((const char*)leaf, leaf_addr, sizeof(Leaf_kv), cxt);

#else
  // batch write updated leaf and on-chip lock
  RdmaOpRegion rs[2];
  rs[0].source = (uint64_t)leaf;
  rs[0].dest = leaf_addr;
  rs[0].size = sizeof(Leaf_kv);
  rs[0].is_on_chip = false;
  GlobalAddress lock_addr;
  uint64_t mask;
  get_on_chip_lock_addr(leaf_addr, lock_addr, mask);
  rs[1].source = (uint64_t)cas_buffer;  // unlock
  rs[1].dest = lock_addr;
  rs[1].is_on_chip = true;
  dsm->write_cas_mask_sync(rs[0], rs[1], ~0UL, 0UL, mask, cxt);

#endif
#endif
  return;
}
int Tree::faa_buffer_counter_n_write_leaf(const Key &k, Value &v, int depth, GlobalAddress& leaf_addr, int leaf_type ,int klen,int vlen,
                                   const GlobalAddress &e_ptr, GlobalAddress old_e, uint64_t *ret_buffer,
                                   CoroContext *cxt, int coro_id)
{
    auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
    new (leaf_buffer) Leaf_kv(e_ptr,leaf_type,klen,vlen,k, v);
    if(leaf_addr == GlobalAddress::Null())    leaf_addr = dsm->alloc(sizeof(Leaf_kv));

    auto faa_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    auto faa_addr = GADD(old_e,sizeof(GlobalAddress) + 256*sizeof(BufferEntry));


/*
    RdmaOpRegion rs[2];
    memset(rs,0,sizeof(RdmaOpRegion)*2);
    rs[0].source     = (uint64_t)leaf_buffer;
    rs[0].dest       = leaf_addr.val;
    rs[0].size       = sizeof(Leaf_kv);
    rs[0].is_on_chip = false;
    rs[1].source     = (uint64_t)faa_buffer;
    rs[1].dest       = faa_addr.val;
    rs[1].size       = 1;
    rs[1].is_on_chip = false;*/
    dsm->faa_sync(faa_addr,(1UL<<16),faa_buffer,cxt);
    // dsm->write_faa_sync(rs[0], rs[1],(1UL<<16),cxt);   //直接把counter1搞成两个字节
    // dsm->faa_boundary(faa_addr,(1<<32),faa_buffer,~0UL,false,cxt);

                //  auto buffer_buffer1 =  (dsm->get_rbuf(coro_id)).get_buffer_buffer();
            //  read_buffer_node(old_e, buffer_buffer1,0, depth, true,cxt, coro_id);

    int idx =  (*faa_buffer & (uint64_t)0xFFFF << 16) >> 16;
    if(idx <256)     dsm->write_sync(leaf_buffer, leaf_addr,sizeof(Leaf_kv), cxt);
    return idx;
}

//向缓冲节点空槽插入
bool Tree::out_of_place_write_leaf(const Key &k, Value &v, int depth, GlobalAddress& leaf_addr, int leaf_type ,int klen,int vlen,
                                   const GlobalAddress &e_ptr, BufferEntry &old_e, uint64_t *ret_buffer,
                                   CoroContext *cxt, int coro_id) {
  bool unwrite = leaf_addr == GlobalAddress::Null();
  auto slot_buffer =(char *) (dsm->get_rbuf(coro_id)).get_cas_buffer();


  // allocate & write
  /*
  if (unwrite) {  // !ONLY allocate once
    auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
    new (leaf_buffer) Leaf_kv(e_ptr,leaf_type,klen,vlen,k, v);
    leaf_addr = dsm->alloc(sizeof(Leaf_kv));
    // write_cnt[dsm->getMyThreadID()]++;
    // auto write_start = std::chrono::high_resolution_clock::now();
    dsm->write_sync(leaf_buffer, leaf_addr,sizeof(Leaf_kv), cxt);
    // auto write_stop = std::chrono::high_resolution_clock::now();
    // auto write_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(write_stop - write_start);
    // write_time[dsm->getMyThreadID()] += write_duration.count();
  }
  else {  // write the changed e_ptr inside leaf
    auto ptr_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
    *ptr_buffer = e_ptr;
    // dsm->write((const char *)ptr_buffer, leaf_addr, sizeof(GlobalAddress), false, cxt);
  }
*/
  // cas entry
   new(slot_buffer) BufferEntry(0,get_partial(k,depth-1),1,leaf_type,leaf_addr);  
   dsm->write_sync(slot_buffer,e_ptr,8, cxt); 

  auto remote_cas = [=](){
    cas_cnt[dsm->getMyThreadID()] ++;
    // auto cas_start = std::chrono::high_resolution_clock::now();
    // bool res=dsm->cas_sync(e_ptr, (uint64_t)old_e, (uint64_t)new_e, ret_buffer, cxt); 
    // auto cas_stop = std::chrono::high_resolution_clock::now();
    // auto cas_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(cas_stop - cas_start);
    // cas_time[dsm->getMyThreadID()] += cas_duration.count();   
    // return res;
  };


  // bool res=remote_cas();
  // if(res) old_e = new_e;

  return true;

}


bool Tree::read_node(InternalEntry &p, bool& type_correct, char *node_buffer, const GlobalAddress& p_ptr, int depth, bool from_cache,
                     CoroContext *cxt, int coro_id) {
  // auto read_size = sizeof(GlobalAddress) + sizeof(Header) + node_type_to_num(p.type()) * sizeof(InternalEntry) ;
  auto read_size = sizeof(GlobalAddress) + sizeof(Header) + 256 * sizeof(InternalEntry) + 1;
  dsm->read_sync(node_buffer, p.addr(), read_size, cxt);

  auto p_node = (InternalPage *)node_buffer;
  auto& hdr = p_node->hdr;
  read_internal_node_type_cnt[dsm->getMyThreadID()][hdr.type()] ++;

  if (hdr.node_type != p.node_type) {
    if (hdr.node_type > p.node_type) {  // need to read the rest part
      read_node_repair[dsm->getMyThreadID()] ++;
      auto remain_size = (node_type_to_num(hdr.type()) - node_type_to_num(p.type())) * sizeof(InternalEntry);
      // dsm->read_sync(node_buffer + read_size, GADD(p.addr(), read_size), remain_size, cxt);
    }
    p.node_type = hdr.node_type;
    type_correct = false;
  }
  else type_correct = true;
  // udpate reverse pointer if needed
  if ( p_node->rev_ptr != p_ptr) {
    auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    dsm->cas(p.addr(), p_node->rev_ptr, p_ptr, cas_buffer, false, cxt);
    // dsm->cas_sync(p.addr(), p_node->rev_ptr, p_ptr, cas_buffer, cxt);
  }
  return p_node->is_valid(p_ptr, depth,from_cache);
}

bool Tree::read_node_from_buffer(BufferEntry &p, bool& type_correct, char *node_buffer, const GlobalAddress& p_ptr, int depth, bool from_cache,
                     CoroContext *cxt, int coro_id) {
  auto read_size = sizeof(GlobalAddress) + sizeof(Header) + node_type_to_num(p.type()) * sizeof(InternalEntry);
  dsm->read_sync(node_buffer, p.addr(), read_size, cxt);
  auto p_node = (InternalPage *)node_buffer;
  auto& hdr = p_node->hdr;
  if (hdr.node_type != p.leaf_type) {
    if (hdr.node_type > p.leaf_type) {  // need to read the rest part
      read_node_repair[dsm->getMyThreadID()] ++;
      auto remain_size = (node_type_to_num(hdr.type()) - node_type_to_num(p.type())) * sizeof(InternalEntry);
      dsm->read_sync(node_buffer + read_size, GADD(p.addr(), read_size), remain_size, cxt);
    }
    p.leaf_type = hdr.node_type;
    type_correct = false;
  }
  else type_correct = true ;

  // udpate reverse pointer if needed
  if ( p_node->rev_ptr != p_ptr) {
    auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    dsm->cas(p.addr(), p_node->rev_ptr, p_ptr, cas_buffer, false, cxt);

    // dsm->cas_sync(p.addr(), p_node->rev_ptr, p_ptr, cas_buffer, cxt);
  }
  return p_node->is_valid(p_ptr, depth,from_cache);
}

//读出一个buffer node并且验证其正确性  
bool Tree::read_buffer_node(GlobalAddress node_addr, char *node_buffer, const GlobalAddress& p_ptr, int depth, bool from_cache,   //只需要判断反向指针对不对就可以了 （有没有分裂）
                     CoroContext *cxt, int coro_id) {
  size_t read_size = 0;
  read_size += sizeof(GlobalAddress) + sizeof(BufferHeader) + 256*sizeof(BufferEntry) +1;
  dsm->read_sync(node_buffer, node_addr, read_size, cxt);

  auto p_node = (InternalBuffer *)node_buffer;
      
  read_buffer_node_type_cnt[dsm->getMyThreadID()] ++;
  // udpate reverse pointer if needed
  if (!from_cache &&p_node->rev_ptr != p_ptr) {
    auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    dsm->cas(node_addr, p_node->rev_ptr, p_ptr, cas_buffer, false, cxt);

    // dsm->cas_sync(p.addr(), p_node->rev_ptr, p_ptr, cas_buffer, cxt);
  }
  return p_node->is_valid(p_ptr, depth,from_cache);
}

//新建一个内部节点、缓冲节点和叶节点
bool Tree::out_of_place_write_node(const Key &k, Value &v,const int depth_i, GlobalAddress& leaf_addr, int leaf_type,int klen,int vlen,int partial_len,uint8_t diff_partial,
                                   const GlobalAddress &e_ptr, const InternalEntry &old_e,const GlobalAddress& node_addr,
                                   uint64_t *ret_buffer, CoroContext *cxt, int coro_id) {
  int depth = depth_i;
  int new_node_num = partial_len / (define::hPartialLenMax + 1) + 1;
  auto leaf_unwrite = (leaf_addr == GlobalAddress::Null());

  // allocate node
  GlobalAddress *node_addrs = new GlobalAddress[new_node_num];
  GlobalAddress bnode_addr = dsm->alloc(sizeof(InternalBuffer));
  // 只有一个叶节点的情况
  // map_buffer_cnt[bnode_addr.val] = 1;

  dsm->alloc_nodes(new_node_num, node_addrs);

  // allocate & write new leaf
  auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
  auto leaf_e_ptr = GADD(bnode_addr, sizeof(GlobalAddress));
 // printf("leaf buffer:  %d\n",leaf_buffer);
  if (leaf_unwrite) {  // !ONLY allocate once
    new (leaf_buffer) Leaf_kv(leaf_e_ptr,leaf_type,klen,vlen,k, v);
    leaf_addr = dsm->alloc(sizeof(Leaf_kv));
  }
  else {  // write the changed e_ptr inside new leaf  TODO: batch
    auto ptr_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
    *ptr_buffer = leaf_e_ptr;
    dsm->write((const char *)ptr_buffer, leaf_addr, sizeof(GlobalAddress), false, cxt);
  }
//  printf("internal node addr:  %" PRIu64" bnode addr: %" PRIu64" leaf addr:  %" PRIu64"\n",node_addrs[0].val,bnode_addr.val,leaf_addr.val);
  // init inner nodes
  NodeType nodes_type = num_to_node_type(2);
  InternalPage ** node_pages = new InternalPage* [new_node_num];
  auto rev_ptr = e_ptr;
  for (int i = 0; i < new_node_num -1; ++ i) {
    auto node_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
 //   printf("internal node buffer:  %d\n",node_buffer);
    node_pages[i] = new (node_buffer) InternalPage(k, define::hPartialLenMax, depth, nodes_type, rev_ptr);
    node_pages[i]->records[0] = InternalEntry(get_partial(k, depth + define::hPartialLenMax),
                                              nodes_type, node_addrs[i + 1]);
    rev_ptr = GADD(node_addrs[i], sizeof(GlobalAddress));
    partial_len -= define::hPartialLenMax + 1;
    depth += define::hPartialLenMax + 1;
  }
  { 
    auto node_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
 //   printf("internal node buffer:  %d\n",node_buffer);
    node_pages[new_node_num -1] = new (node_buffer) InternalPage(k, partial_len, depth, nodes_type, rev_ptr);
    depth += partial_len + 1;
    node_pages[new_node_num -1]->records[0] = InternalEntry(diff_partial,old_e);   
    node_pages[new_node_num -1]->records[1] = InternalEntry(get_partial(k,depth - 1),1,bnode_addr);
     //     printf("thread  %d 7 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(node_pages[new_node_num -1]->hdr));
  }
  // init buffer nodes
  auto b_buffer = (dsm->get_rbuf(coro_id)).get_buffer_buffer();
 //   printf("buffer node buffer:  %d\n",b_buffer);
 // if(node_addrs[0].val == 0) printf("0003!\n");
  InternalBuffer* buffernode = new (b_buffer) InternalBuffer(k,define::bPartialLenMax,depth,1,2,node_addrs[0]);  // 暂时定初始2B作为partial key buffer地址
      //    printf("thread  %d 8 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(buffernode->hdr));
  buffernode->records[0] = BufferEntry(0,get_partial(k, depth + buffernode->hdr.partial_len ),1,leaf_type,leaf_addr);
  // init the parent entry
  auto new_e = InternalEntry(old_e.partial,2,nodes_type, node_addrs[0]);
  auto page_size = sizeof(GlobalAddress) + sizeof(Header) + 256 * sizeof(InternalEntry) + 1;

  // batch_write nodes (doorbell batching)
  int i;
  RdmaOpRegion *rs =  new RdmaOpRegion[new_node_num + 2];
  for (i = 0; i < new_node_num; ++ i) {
    rs[i].source     = (uint64_t)node_pages[i];
    rs[i].dest       = node_addrs[i];
    rs[i].size       = page_size;
    rs[i].is_on_chip = false;
  }
  {
    rs[new_node_num].source     = (uint64_t)b_buffer;
    rs[new_node_num].dest       = bnode_addr;
    rs[new_node_num].size       = sizeof(InternalBuffer);
    rs[new_node_num].is_on_chip = false;
  }
  if (leaf_unwrite) {
    rs[new_node_num + 1].source     = (uint64_t)leaf_buffer;
    rs[new_node_num + 1].dest       = leaf_addr;
    rs[new_node_num + 1].size       = sizeof(Leaf_kv);
    rs[new_node_num + 1].is_on_chip = false;
  }
  dsm->write_batches_sync(rs,new_node_num + 2 , cxt, coro_id);

  // cas
  auto remote_cas = [=](){
    bool res=dsm->cas_sync(e_ptr, (uint64_t)old_e, (uint64_t)new_e, ret_buffer, cxt);
    return res;
  };
  auto reclaim_memory = [=](){
    for (int i = 0; i < new_node_num; ++ i) {
      dsm->free(node_addrs[i], define::allocAlignPageSize);
    }
  };
// #ifndef TREE_TEST_ROWEX_ART
  bool res = remote_cas();
// #else
//   bool res = lock_and_cas_in_node(node_addr, remote_cas, cxt, coro_id);
// #endif
  if (!res) reclaim_memory();

  // cas the updated rev_ptr and depth inside buffer node 
  if (res) {
    auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    dsm->cas(old_e.addr(), e_ptr, GADD(node_addrs[new_node_num - 1], sizeof(GlobalAddress)), cas_buffer, false, cxt);
  }

#ifdef USE_CN_CACHE
  if (res) {   //将内部节点和缓冲节点都加入cache
    for (int i = 0; i < new_node_num; ++ i) {
    //  printf("thread  %d 9 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(node_pages[i]->hdr));
      index_cache->add_to_cache(k, 0,node_pages[i], GADD(node_addrs[i], sizeof(GlobalAddress)));
    }
//printf("thread  %d 10 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(buffernode->hdr));
    // index_cache->add_to_cache(k, 1,(InternalPage *)buffernode, GADD(bnode_addr, sizeof(GlobalAddress) + sizeof(BufferHeader)));
  }
#endif  

  // free
  delete[] rs; delete[] node_pages; delete[] node_addrs;
  return res;
}


bool Tree::out_of_place_write_node_from_buffer(const Key &k, Value &v,const int depth_i, GlobalAddress& leaf_addr, int leaf_type,int klen,int vlen,int partial_len,uint8_t diff_partial,
                                   const GlobalAddress &e_ptr, const BufferEntry &old_e, const GlobalAddress& node_addr,
                                   uint64_t *ret_buffer, CoroContext *cxt, int coro_id) {
  int depth = depth_i;                           
  int new_node_num = partial_len / (define::hPartialLenMax + 1) + 1;
  auto leaf_unwrite = (leaf_addr == GlobalAddress::Null());

  // allocate node
  GlobalAddress *node_addrs = new GlobalAddress[new_node_num];
  GlobalAddress bnode_addr = dsm->alloc(sizeof(InternalBuffer));
  dsm->alloc_nodes(new_node_num, node_addrs);


  // allocate & write new leaf
  auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
  auto leaf_e_ptr = GADD(bnode_addr, sizeof(GlobalAddress) + sizeof(BufferHeader) + sizeof(BufferEntry) * 1);

  if (leaf_unwrite) {  // !ONLY allocate once
    new (leaf_buffer) Leaf_kv(leaf_e_ptr,leaf_type,klen,vlen,k, v);
    leaf_addr = dsm->alloc(sizeof(Leaf_kv));
  }
  else {  // write the changed e_ptr inside new leaf  TODO: batch
    auto ptr_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
    *ptr_buffer = leaf_e_ptr;
    dsm->write((const char *)ptr_buffer, leaf_addr, sizeof(GlobalAddress), false, cxt);
  }

  // init inner nodes
  NodeType nodes_type = num_to_node_type(2);
  InternalPage ** node_pages = new InternalPage* [new_node_num];
  auto rev_ptr = e_ptr;
  for (int i = 0; i < new_node_num - 1; ++ i) {
    auto node_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
    node_pages[i] = new (node_buffer) InternalPage(k, define::hPartialLenMax, depth, nodes_type, rev_ptr);
    node_pages[i]->records[0] = InternalEntry(get_partial(k, depth + define::hPartialLenMax),
                                              nodes_type, node_addrs[i + 1]);
    rev_ptr = GADD(node_addrs[i], sizeof(GlobalAddress) + sizeof(Header));
    partial_len -= define::hPartialLenMax + 1;
    depth += define::hPartialLenMax + 1;
  }
  {
    auto node_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
 //   printf("internal node buffer:  %d\n",node_buffer);
    node_pages[new_node_num -1] = new (node_buffer) InternalPage(k, partial_len, depth, nodes_type, rev_ptr);
    depth += partial_len + 1;
    node_pages[new_node_num -1]->records[0] = InternalEntry(diff_partial,old_e);
    node_pages[new_node_num -1]->records[1] = InternalEntry(get_partial(k,depth-1),1,bnode_addr);
       //       printf("thread  %d 11 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(node_pages[new_node_num -1]->hdr));
  }

  // init buffer nodes
  auto b_buffer = (dsm->get_rbuf(coro_id)).get_buffer_buffer();
 // if(node_addrs[0].val == 0) printf("0004!\n");
  InternalBuffer* buffernode = new (b_buffer) InternalBuffer(k,define::bPartialLenMax,depth ,1,0,node_addrs[0]);  // 暂时定初始2B作为partial key buffer地址
         //   printf("thread  %d 12 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(buffernode->hdr));
  buffernode->records[0] = BufferEntry(0,get_partial(k, depth + buffernode->hdr.partial_len ),1,leaf_type,leaf_addr);
  
  // init the parent entry
  auto new_e = BufferEntry(2,old_e.partial, 1,nodes_type, node_addrs[0]);
  auto page_size = sizeof(GlobalAddress) + sizeof(Header) + node_type_to_num(nodes_type) * sizeof(InternalEntry);

  // batch_write nodes (doorbell batching)
  int i;
  RdmaOpRegion *rs =  new RdmaOpRegion[new_node_num + 2];
  for (i = 0; i < new_node_num; ++ i) {
    rs[i].source     = (uint64_t)node_pages[i];
    rs[i].dest       = node_addrs[i];
    rs[i].size       = page_size;
    rs[i].is_on_chip = false;
  }
  {
    rs[new_node_num].source     = (uint64_t)buffernode;
    rs[new_node_num].dest       = bnode_addr;
    rs[new_node_num].size       = sizeof(InternalBuffer);
    rs[new_node_num].is_on_chip = false;

  }
  if (leaf_unwrite) {
    rs[new_node_num + 1].source     = (uint64_t)leaf_buffer;
    rs[new_node_num + 1].dest       = leaf_addr;
    rs[new_node_num + 1].size       = sizeof(Leaf_kv);
    rs[new_node_num + 1].is_on_chip = false;
  }
  dsm->write_batches_sync(rs, (leaf_unwrite ? new_node_num + 2 : new_node_num +1), cxt, coro_id);

  // cas
  auto remote_cas = [=](){
    bool res=dsm->cas_sync(e_ptr, (uint64_t)old_e, (uint64_t)new_e, ret_buffer, cxt);
    return res;
  };
  auto reclaim_memory = [=](){
    for (int i = 0; i < new_node_num; ++ i) {
      dsm->free(node_addrs[i], define::allocAlignPageSize);
    }
  };
// #ifndef TREE_TEST_ROWEX_ART
  bool res = remote_cas();
// #else
//   bool res = lock_and_cas_in_node(node_addr, remote_cas, cxt, coro_id);
// #endif
  if (!res) reclaim_memory();

  // cas the updated rev_ptr inside old leaf / old node
  if (res) {
    auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    dsm->cas(old_e.addr(), e_ptr, GADD(node_addrs[new_node_num - 1], sizeof(GlobalAddress) + sizeof(Header)), cas_buffer, false, cxt);
  }

#ifdef USE_CN_CACHE
  if (res) {   //将内部节点和缓冲节点都加入cache
    for (int i = 0; i < new_node_num; ++ i) {
       //     printf("thread  %d 13 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(node_pages[i]->hdr));
      index_cache->add_to_cache(k, 0,node_pages[i], GADD(node_addrs[i], sizeof(GlobalAddress)));
    }
 //   printf("thread  %d 14 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(buffernode->hdr));
    // index_cache->add_to_cache(k, 1,(InternalPage *)buffernode, GADD(bnode_addr, sizeof(GlobalAddress) + sizeof(BufferHeader)));
  }
#endif

  // free
  delete[] rs; delete[] node_pages; delete[] node_addrs;
  return res;
}

void Tree::cas_node_type(NodeType next_type, GlobalAddress p_ptr, InternalEntry p, Header hdr,   //在这里没cas成功？？？？
                         CoroContext *cxt, int coro_id) {
  auto node_addr = p.addr();
  auto header_addr = GADD(node_addr, sizeof(GlobalAddress) + 256*sizeof(InternalEntry));
  auto cas_buffer_1 = (dsm->get_rbuf(coro_id)).get_cas_buffer();
  auto cas_buffer_2 = (dsm->get_rbuf(coro_id)).get_cas_buffer();
  auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
  std::pair<bool, bool> res = std::make_pair(false, false);

  // batch cas old_entry & node header to change node type
  auto remote_cas_both = [=, &p_ptr, &p, &hdr](){
    auto new_e = InternalEntry(next_type, p);
    RdmaOpRegion rs[2];
    rs[0].source     = (uint64_t)cas_buffer_1;
    rs[0].dest       = p_ptr;
    rs[0].is_on_chip = false;
    rs[1].source     = (uint64_t)cas_buffer_2;
    rs[1].dest       = header_addr;
    rs[1].is_on_chip = false;
    std::pair<bool, bool> res=dsm->two_cas_mask_sync(rs[0], (uint64_t)p, (uint64_t)new_e, ~0UL,rs[1], hdr, Header(next_type,hdr), ~0UL, cxt);

    return res;
  };

  // only cas old_entry
  auto remote_cas_entry = [=, &p_ptr, &p](){
    auto new_e = InternalEntry(next_type, p);
    return dsm->cas_sync(p_ptr, (uint64_t)p, (uint64_t)new_e, cas_buffer_1, cxt);
  };

  // only cas node_header
  auto remote_cas_header = [=, &hdr](){
    return dsm->cas_mask_sync(header_addr, hdr, Header(next_type,hdr), cas_buffer_2, Header::node_type_mask, cxt);
  };

  // read down to find target entry when split
  auto read_first_entry = [=, &p_ptr, &p](){
    p_ptr = GADD(p.addr(), sizeof(GlobalAddress));
    dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
    p = *(InternalEntry *)entry_buffer;
  };

re_switch:
  auto old_res = res;
  if (!old_res.first && !old_res.second) {
    res = remote_cas_both();
  }
  else {
    if (!old_res.first)  res.first  = remote_cas_entry();
    if (!old_res.second) res.second = remote_cas_header();
  }
  if (!res.first) {
    p = *(InternalEntry *)cas_buffer_1;
    // handle the conflict when switch & split/delete happen at the same time
    while (p != InternalEntry::Null() && p.node_type != 1 && p.addr() != node_addr) {
      read_first_entry();
      retry_cnt[dsm->getMyThreadID()][SWITCH_FIND_TARGET] ++;
    }
    if (p.addr() != node_addr || p.type() >= next_type) res.first = true;  // no need to retry
  }
  if (!res.second) {
    hdr = *(Header *)cas_buffer_2;
    if (hdr.type() >= next_type) res.second = true;  // no need to retry
  }
  if (!res.first || !res.second) {
    retry_cnt[dsm->getMyThreadID()][SWITCH_RETRY] ++;
    goto re_switch;
  }
}
void Tree::cas_node_type_from_buffer(NodeType next_type, GlobalAddress p_ptr, BufferEntry p, Header hdr,
                         CoroContext *cxt, int coro_id) {
  auto node_addr = p.addr();
  auto header_addr = GADD(node_addr, sizeof(GlobalAddress));
  auto cas_buffer_1 = (dsm->get_rbuf(coro_id)).get_cas_buffer();
  auto cas_buffer_2 = (dsm->get_rbuf(coro_id)).get_cas_buffer();
  auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
  std::pair<bool, bool> res = std::make_pair(false, false);
  auto new_e = BufferEntry(next_type, p);
  // batch cas old_entry & node header to change node type
  auto remote_cas_both = [=, &p_ptr, &p, &hdr](){
    auto new_e = BufferEntry(next_type, p);
    RdmaOpRegion rs[2];
    rs[0].source     = (uint64_t)cas_buffer_1;
    rs[0].dest       = p_ptr;
    rs[0].is_on_chip = false;
    rs[1].source     = (uint64_t)cas_buffer_2;
    rs[1].dest       = header_addr;
    rs[1].is_on_chip = false;
    std::pair<bool, bool> res=dsm->two_cas_mask_sync(rs[0], (uint64_t)p, (uint64_t)new_e, ~0UL,
                                  rs[1], hdr, Header(next_type,hdr), Header::node_type_mask, cxt);

    return res;
  };

  // only cas old_entry
  auto remote_cas_entry = [=, &p_ptr, &p](){
    auto new_e = BufferEntry(next_type, p);
    return dsm->cas_sync(p_ptr, (uint64_t)p, (uint64_t)new_e, cas_buffer_1, cxt);
  };

  // only cas node_header
  auto remote_cas_header = [=, &hdr](){
    return dsm->cas_mask_sync(header_addr, hdr, Header(next_type,hdr), cas_buffer_2, Header::node_type_mask, cxt);
  };

  // read down to find target entry when split
  auto read_first_entry = [=, &p_ptr, &p](){
    p_ptr = GADD(p.addr(), sizeof(GlobalAddress));
    dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(BufferEntry), cxt);
    p = *(BufferEntry *)entry_buffer;
  };

re_switch:
  auto old_res = res;
  if (!old_res.first && !old_res.second) {
    res = remote_cas_both();
  }
  else {
    if (!old_res.first)  res.first  = remote_cas_entry();
    if (!old_res.second) res.second = remote_cas_header();
  }
  if (!res.first) {
    p = *(BufferEntry *)cas_buffer_1;
    // handle the conflict when switch & split/delete happen at the same time
    while (p != BufferEntry::Null() && p.node_type != 1 && p.addr() != node_addr) {
      read_first_entry();
      retry_cnt[dsm->getMyThreadID()][SWITCH_FIND_TARGET] ++;
    }
    if (p.addr() != node_addr || p.type() >= next_type) res.first = true;  // no need to retry
  }
  if (!res.second) {
    hdr = *(Header *)cas_buffer_2;
    if (hdr.type() >= next_type) res.second = true;  // no need to retry
  }
  if (!res.first || !res.second) {
    retry_cnt[dsm->getMyThreadID()][SWITCH_RETRY] ++;
    goto re_switch;
  }
}
//新建很多个缓冲节点 有重复的往里面放  并且还要去重
bool Tree::out_of_place_write_buffer_node(const Key &k, Value &v, int depth,InternalBuffer* bnode,int leaf_type,int klen,int vlen,GlobalAddress leaf_addr,CacheEntry**&entry_ptr_ptr,CacheEntry*& entry_ptr,bool from_cache,InternalEntry& old_e, GlobalAddress p_ptr,CoroContext *cxt, int coro_id) {
return false;
}

int Tree::find_next_diff(Leaf_kv* leaves, int leaf_cnt, int depth){
  // 找到公共前缀的长度
  int res = 0;
  assert(depth > 0);
  for(int i = depth; ; i++){
    char cur = get_partial(leaves[0].key,i);
    for(int j = 1; j < leaf_cnt; j ++){
      auto l = leaves[j];
      if(i > 128 || get_partial(l.key,i) != cur)
        return i - depth;
    }
  }
  return 0;
}


bool Tree::out_of_place_write_buffer_node_new(const Key &k, Value &v, int depth,InternalBuffer* bnode,int leaf_type,int klen,int vlen,GlobalAddress leaf_addr,CacheEntry**&entry_ptr_ptr,CacheEntry*& entry_ptr,std::vector<InternalEntry> buffer_slot,bool from_cache,bool buffer_from_cache_flag,InternalEntry& old_e, GlobalAddress p_ptr,bool &buffer_type_change ,CoroContext *cxt, int coro_id) {
  //先获取锁 再修改 否则不修改  搞异地更新吧 ！！！！！
  static const uint64_t lock_cas_offset = ROUND_DOWN(STRUCT_OFFSET(InternalBuffer, lock_byte), 3);  //8B对齐
  static const uint64_t lock_mask       = 1UL << ((STRUCT_OFFSET(InternalBuffer, lock_byte) - lock_cas_offset) * 8);
  auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
  auto acquire_lock = dsm->cas_mask_sync(GADD(old_e.addr(), lock_cas_offset), 0UL, ~0UL, cas_buffer, lock_mask, cxt);

  if(!acquire_lock) return false;

  depth ++;
// if(buffer_from_cache_flag) assert(cache_entry_buffer->records.size() == 256);
  int leaf_cnt = 256;
  int leaf_entry_cnt[256];  //记录在bnode 的槽里面partialkey一致的叶子的数量
  std::vector<RdmaOpRegion> rs;
  int new_bnode_num = 0;
  int leaf_flag = 0; //叶节点的部分键是否重复
  BufferEntry *new_leaf_be;
  GlobalAddress *bnode_addrs; 

  // leaf_flag?  dsm->alloc_bnodes(new_bnode_num +1, bnode_addrs) :dsm->alloc_bnodes(new_bnode_num+1+1, bnode_addrs);  //最后一个是异地的内部节点的新地址
  auto leaves_buffer =(dsm->get_rbuf(coro_id)).get_range_buffer();
  auto buffer_buffer =  (dsm->get_rbuf(coro_id)).get_buffer_buffer(); 
  for(int i =0;i<256;i++)  //把所有叶子读过来
  {
  if(buffer_from_cache_flag && bnode->records[i].val == 0)   bnode->records[i].val = buffer_slot[i].val;
  while(bnode->records[i].val == 0)
  {
#ifdef TEST_TIME
      auto read_buffer_node_start = std::chrono::high_resolution_clock::now();
#endif
      
      bool is_valid = read_buffer_node(old_e.addr(), buffer_buffer, p_ptr, depth -1, from_cache,cxt, coro_id);

#ifdef TEST_TIME

      auto read_buffer_node_stop = std::chrono::high_resolution_clock::now();
      auto read_buffer_node_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(read_buffer_node_stop - read_buffer_node_start);  
      read_buffer_node_time[0][dsm->getMyThreadID()] += read_buffer_node_duration.count();  
      // read_buffer_node_time_this += read_buffer_node_duration.count();  
#endif
      bnode = (InternalBuffer *)buffer_buffer;
      if(bnode->hdr.count_1 < 256) 
      {
          auto release_lock = dsm->cas_mask_sync(GADD(old_e.addr(), lock_cas_offset), ~0UL, 0UL, cas_buffer, lock_mask, cxt);
          return false;
      }
  }
     RdmaOpRegion r;
        r.dest       = bnode->records[i].addr();
        r.source = (uint64_t)leaves_buffer + i * define::allocAlignPageSize;
        // assert(r.dest !=0);
        r.size       = sizeof(Leaf_kv);
        r.is_on_chip = false;
        rs.push_back(r);
  }
  InternalBuffer old_b = *bnode;
  //读需要放在下一层的叶节点 read_batch
  dsm->read_batches_new_sync(rs,cxt,coro_id);   //没读过来？？？搞成单次读呢？
  //写叶节点
  auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
  
  if(leaf_addr == GlobalAddress::Null()) leaf_addr = dsm->alloc(sizeof(Leaf_kv));


  Leaf_kv *leaves = new Leaf_kv [leaf_cnt];
  int leaf_no_repeat_cnt = 0;
  //读到了leaves_buffer
  for(int i = 0;i<leaf_cnt;i++)
  {
    leaves[i] = *(Leaf_kv *)(leaves_buffer + i * define::allocAlignPageSize);
  }

  uint8_t new_leaf_partial = get_partial(k,depth-1);
  std::set<Key> s;
  std::map<char,std::vector<int>> mp;
  bool update_flag = false;
  int reapeat_time = 0;
  for(int i = 255; i >= 0; i --){
    Key& tmp_k = leaves[i].key;
    char c = bnode->records[i].partial; // 不太确定这里拿到的是不是下一个字节
    if(s.find(tmp_k) == s.end()){  // s里面找不到
      if(tmp_k == k)  //有的话更新
      {
        auto update_leaf =(Leaf_kv*) (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
        memcpy(update_leaf,&leaves[i],sizeof(Leaf_kv));
        in_place_update_leaf(k,v,bnode->records[i].addr(),leaf_type,update_leaf,cxt,coro_id); 
        update_flag = true;
      }
      mp[c].push_back(i);
      s.insert(tmp_k);
    }
    else
    reapeat_time ++;
  }
  int empty_slot = 256 - s.size() - (update_flag == false);
  if(empty_slot > define::threshold )
  { int count = 0;
    // GlobalAddress new_old_page_addr = dsm->alloc(sizeof(InternalBuffer)); //还是搞成异地写 得多一次cas
    auto old_page_buffer = (dsm->get_rbuf(coro_id)).get_buffer_buffer();
    InternalBuffer * old_page;
    old_page = new (old_page_buffer) InternalBuffer();
    old_page->rev_ptr = bnode->rev_ptr;
    old_page->hdr = bnode->hdr;
    int idx = 0;
    for(auto& it:mp){
      auto& v = it.second;
      for(auto& i : v){
        old_page->records[idx ++] = bnode->records[i];
      }
    }
    old_page->hdr.count_1  = s.size();
    count =  s.size();
    // 保存.val
    // map_buffer_cnt[new_old_page_addr.val] = s.size();
    old_page->unlock();
    assert(old_page->hdr.count_1 <256);
    if(!update_flag){
      BufferEntry leaf_b_entry(0,get_partial(k,depth-1),1,leaf_type,leaf_addr);
      old_page->records[idx] = leaf_b_entry;
      old_page->hdr.count_1 ++;
      count ++;
      
    }
    new (leaf_buffer) Leaf_kv(GADD(old_e.addr(),sizeof(GlobalAddress)+idx*sizeof(BufferEntry)),leaf_type,klen,vlen,k,v);
    int write_num = update_flag? 1 :2;
    RdmaOpRegion *rs_write =  new RdmaOpRegion[write_num];
    memset(rs_write,0,sizeof(RdmaOpRegion)*(write_num));
    {
      rs_write[0].source     = (uint64_t)old_page_buffer;
      rs_write[0].dest       = old_e.addr();  //是最后一个地址
      rs_write[0].size       = sizeof(InternalBuffer);
      rs_write[0].is_on_chip = false;
    //  dsm->write((const char*)old_bnode_buffer, e_ptr, sizeof(InternalBuffer), false, cxt);
    }
     if(!update_flag){
      rs_write[1].source     = (uint64_t)leaf_buffer;
      rs_write[1].dest       = leaf_addr;
      rs_write[1].size       = sizeof(Leaf_kv);
      rs_write[1].is_on_chip = false;
    //  dsm->write((const char*)leaf_buffer, leaf_addr, sizeof(Leaf_kv), false, cxt);
    }
        dsm->write_batches_sync(rs_write, write_num, cxt, coro_id);
        buffer_type_change = false;

    //在搞一个cas
    auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    InternalEntry new_entry(old_e);
  //  new (cas_node_type_buffer) InternalEntry(new_entry);
    // new_entry.packed_addr = {new_old_page_addr.nodeID, new_old_page_addr.offset >> ALLOC_ALLIGN_BIT};
    new_entry.empty = 1;
    // assert(new_entry.packed_addr.mn_id == 0);
    bool res =dsm->cas_sync(p_ptr, (uint64_t)old_e, (uint64_t)new_entry, cas_buffer, cxt);
    if(res) 
     {   //先失效父节点
        //  if(from_cache)
        // {
          // index_cache->invalidate(entry_ptr_ptr, entry_ptr);  //首先是invalid 父节点 然后在外面invalid缓冲节点本身
        // }
        // if(!from_cache)  //先失效父节点（内部节点） 在这里失效的时候可以直接修改父节点的槽 这里的父节点没有太大必要再去找了 直接从上一层拿了父节点在cache的槽了 不管是不是在cache 现在肯定都存在cache了 新增
#ifdef USE_CN_CACHE
        {
          // bool cache_res = index_cache->search_from_cache(k, entry_ptr_ptr, entry_ptr, parent_parent_type,entry_idx,cache_entry_parent_ptr,cache_entry_parent,first_buffer);
          // index_cache->invalidate(entry_ptr_ptr, entry_ptr);
        }
         //加buffer到cacheindex_cache->add_to_cache(k, 1,(InternalPage*)old_page, GADD(new_old_page_addr, sizeof(GlobalAddress) + sizeof(BufferHeader)));
#endif
      // auto write_buffer = (dsm->get_rbuf(coro_id)).get_header_buffer();
      // BufferHeader* new_hdr;
      // new_hdr = new(write_buffer) BufferHeader(old_b.hdr.depth);
      // new_hdr->count_1 = count;
      // dsm->write((const char*)write_buffer, GADD(old_e.addr(),sizeof(GlobalAddress)), sizeof(BufferHeader), false, cxt);
        return true;
     }
    return false;
  }
  else  // 空槽不足则分裂
  {
    int partial_len = find_next_diff(leaves, leaf_cnt, depth - 1);
    for(int i = depth -1;i<depth-1 +partial_len;i++) 
    {
      if(get_partial(k,i) != get_partial(leaves[0].key,i))
      {
         partial_len = i - (depth-1) ;
         break;   
      }
    }

    int new_node_num = partial_len / (define::hPartialLenMax + 1) + 1;

    // allocate node
    GlobalAddress *node_addrs = new GlobalAddress[new_node_num];
    if(new_node_num>1) dsm->alloc_nodes(new_node_num-1, node_addrs);
    NodeType nodes_type = num_to_node_type(2);
    InternalPage ** node_pages = new InternalPage* [new_node_num];
    auto rev_ptr = p_ptr;
    for (int i = 0; i < new_node_num -1; ++ i) {
      auto node_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
  //   printf("internal node buffer:  %d\n",node_buffer);
  // 这里的depth也有可能不对
      node_pages[i] = new (node_buffer) InternalPage(k, define::hPartialLenMax, depth-1, nodes_type, rev_ptr);
      assert(node_pages[i]->hdr.depth != 0);
      node_pages[i]->records[0] = InternalEntry(get_partial(k, depth-1 + define::hPartialLenMax),
                                                2, node_addrs[i + 1]);
      rev_ptr = GADD(node_addrs[i], sizeof(GlobalAddress));
      partial_len -= define::hPartialLenMax + 1;
      depth += define::hPartialLenMax + 1;
      internal_node_cnt[dsm->getMyThreadID()][node_pages[i]->hdr.type()] ++;
    }
    depth +=partial_len;
    std::set<Key> s1;
    std::map<char,std::vector<int>> mp1;
    new_leaf_partial = get_partial(k,depth-1);
    if(new_node_num == 1 && partial_len ==0) mp1 = mp;
    else
    {
    for(int i = 255; i >= 0; i --){
      Key& tmp_k = leaves[i].key;
      char c = get_partial(leaves[i].key,depth-1); // 不太确定这里拿到的是不是下一个字节
      if(s1.find(tmp_k) == s1.end()){
        mp1[c].push_back(i);
        s1.insert(tmp_k);
      }
    }
    }

    // BufferEntry leaf_b_entry(0,getpartial(k,depth),leaf_type,leaf_addr);
    if(!update_flag) mp1[new_leaf_partial].push_back( -1);
    bnode_addrs = new GlobalAddress[mp1.size()+1];
    NodeType old_page_type = num_to_node_type((int)mp1.size());
    auto old_page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
    // 这里的深度貌似不对
    node_pages[new_node_num-1] = new (old_page_buffer) InternalPage(k,partial_len,depth-1-partial_len,old_page_type,rev_ptr);
    auto &old_page = node_pages[new_node_num - 1];


    // Header new_hdr(bnode->hdr);
    // old_page->hdr.val = new_hdr.val;
    old_page->l_padding = 99;
    old_page->rev_ptr = rev_ptr;
    // old_page->lock_byte = 0;
    assert(old_page->hdr.val !=0);
    internal_node_cnt[dsm->getMyThreadID()][old_page->hdr.type()] ++;
    bnode_addrs = new GlobalAddress[mp1.size()];   //最后一个放转换为内部节点后的buffer的地址 
    dsm->alloc_bnodes(mp1.size(), bnode_addrs);
    buffer_node_cnt[dsm->getMyThreadID()] += mp1.size();
    InternalBuffer **new_bnodes = new InternalBuffer* [mp1.size()];  //预留一个 可能需要给叶节点 
    int slot_idx[256];
    memset(slot_idx,-1,256*sizeof(int));
    // assert(old_page->hdr.node_type )
    // printf("buffer ---> internal type is %d \n",old_page->hdr.node_type);
    // if(old_page->hdr.node_type == 7) assert(mp1.size() >128);
    int vec_size = 0;
    for(auto& it : mp1){
      //char partial = it.first;
      auto& vec = it.second;
      // 这里 new 一个新的buffer，，假设是bf
      old_page->records[new_bnode_num].packed_addr ={bnode_addrs[new_bnode_num].nodeID,bnode_addrs[new_bnode_num].offset >> ALLOC_ALLIGN_BIT} ;
      old_page->records[new_bnode_num].partial = it.first;
      old_page->records[new_bnode_num].child_type = 1;
      assert(old_page->hdr.count == 256);


      int j = 0;
      auto bnode_buffer = (dsm->get_rbuf(coro_id)).get_buffer_buffer();  //可能在这里被覆盖掉了
      new_bnodes[new_bnode_num] = new (bnode_buffer)InternalBuffer();
      vec_size += vec.size();
      for(auto& be : vec){
      if(be == -1)
      {
        new (leaf_buffer) Leaf_kv(GADD(bnode_addrs[new_bnode_num],sizeof(GlobalAddress)+j*sizeof(BufferEntry)),leaf_type,klen,vlen,k,v);
        BufferEntry leaf_b_entry(0,get_partial(k,depth),1,leaf_type,leaf_addr);
        new_bnodes[new_bnode_num]->records[j].val = leaf_b_entry.val;
      }
      else{
        assert(old_b.records[be].packed_addr.offset !=0);
        new_bnodes[new_bnode_num]->records[j].val = old_b.records[be].val; // 这里意思是第 i 个叶子的地址
        new_bnodes[new_bnode_num]->records[j].partial = get_partial(leaves[be].get_key(),depth); 
        // assert(new_bnodes[new_bnode_num]->records[j].val !=0);
        slot_idx[new_bnode_num] = be;  //记录相应buffer的叶子（k）
      }
      assert(new_bnodes[new_bnode_num]->records[j].packed_addr.offset !=0);
      j++;
      }
      new_bnodes[new_bnode_num]->rev_ptr.val = GADD(old_e.addr(),sizeof(GlobalAddress)+new_bnode_num*sizeof(InternalEntry)).val;  
      BufferHeader new_hdr(depth);
      new_bnodes[new_bnode_num]->hdr.val = new_hdr.val;
      new_bnodes[new_bnode_num]->hdr.count_1 = vec.size();
      // 保存.val，应该可以暂时不考虑回收
      // map_buffer_cnt[bnode_addrs[new_bnode_num].val] = vec.size();
      new_bnodes[new_bnode_num]->w_lock = 0;
      new_bnode_num ++;
    }
    if(!update_flag) assert(vec_size == (257 - reapeat_time));
    else assert(vec_size == (256 - reapeat_time));

    // int count_total = 0;
    // for(int i =0;i<new_bnode_num;i++) 
    // {
    //   count_total += new_bnodes[i]->hdr.count_1;
    // }
    // if(!update_flag) assert(count_total ==( 257 - reapeat_time));
    // else assert(count_total == (256 - reapeat_time));
     
    //  printf("internal size is %d\n",mp1.size());
    //整一个write_batch  写所有的缓冲节点和叶节点 还有写旧的叶节点
    /*  */
    int write_num = update_flag? new_bnode_num +1:new_bnode_num +2;
    RdmaOpRegion *rs_write =  new RdmaOpRegion[new_node_num + write_num - 1];
    memset(rs_write,0,sizeof(RdmaOpRegion)*(new_node_num + write_num - 1));

    for (int i = 0; i < new_bnode_num; ++ i) {
      rs_write[i].source     = (uint64_t)new_bnodes[i];
      rs_write[i].dest       = bnode_addrs[i];
      rs_write[i].size       = sizeof(InternalBuffer);
      rs_write[i].is_on_chip = false;
    // dsm->write((const char*)new_bnodes[i], bnode_addrs[i], sizeof(InternalBuffer), false, cxt);
    }
    if(!update_flag){
      rs_write[new_bnode_num].source     = (uint64_t)leaf_buffer;
      rs_write[new_bnode_num].dest       = leaf_addr;
      rs_write[new_bnode_num].size       = sizeof(Leaf_kv);
      rs_write[new_bnode_num].is_on_chip = false;
    //  dsm->write((const char*)leaf_buffer, leaf_addr, sizeof(Leaf_kv), false, cxt);
    }
    // auto new_e = InternalEntry(old_e.partial,2,nodes_type, node_addrs[0]);
    auto page_size = sizeof(GlobalAddress) + sizeof(Header) + 256 * sizeof(InternalEntry) +1;

    // batch_write nodes (doorbell batching)
    for (int i = 0; i < new_node_num - 1; ++ i) {
      int j = i + write_num-1;
      rs_write[j].source     = (uint64_t)node_pages[i];
      rs_write[j].dest       = node_addrs[i];
      rs_write[j].size       = page_size;
      rs_write[j].is_on_chip = false;
    }
    {
      rs_write[new_node_num + write_num - 2].source     = (uint64_t)old_page_buffer;
      rs_write[new_node_num + write_num - 2].dest       = old_e.addr();  //是最后一个地址
      rs_write[new_node_num + write_num - 2].size       = sizeof(InternalPage);
      rs_write[new_node_num + write_num - 2].is_on_chip = false;
    //  dsm->write((const char*)old_bnode_buffer, e_ptr, sizeof(InternalBuffer), false, cxt);
    }


    dsm->write_batches_sync(rs_write, new_node_num + write_num - 1, cxt, coro_id);
    auto cas_node_type_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    InternalEntry new_entry(old_e);
    new_entry.child_type = 2;
    new_entry.node_type = static_cast<uint8_t>(old_page_type);
    // new_entry.packed_addr = {node_addrs[0].nodeID, node_addrs[0].offset >> ALLOC_ALLIGN_BIT};
    bool res =dsm->cas_sync(p_ptr, (uint64_t)old_e, (uint64_t)new_entry, cas_node_type_buffer, cxt);

    // assert(res == true && new_entry.child_type == 2);

    //先失效 再加
    // if(from_cache)
#ifdef USE_CN_CACHE
    // {
    //   index_cache->invalidate(entry_ptr_ptr, entry_ptr);  //首先是invalid 父节点 然后在外面invalid缓冲节点本身
    // }
#endif

  // old_e = *(InternalEntry*) cas_node_type_buffer;
  if(res)
  {
#ifdef USE_CN_CACHE
    for(int i =0;i<new_node_num;i++)
    {
      // CacheEntry* ca_ptr;
      index_cache->add_to_cache(k, 0,(InternalPage*)node_pages[i], GADD(node_addrs[i], sizeof(GlobalAddress)));  
      // assert(node_pages[i]->hdr.depth <7);    
      // assert(ca_ptr->depth <7);  
    }
    //加buffer到cache
    /*
    for (int i = 0; i < new_bnode_num; ++ i) {
            // CacheEntry* ca_ptr;
        // printf("thread  %d 16 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(new_bnodes[i]->hdr));
      if(slot_idx[i] == -1) index_cache->add_to_cache(k,1,(InternalPage*)new_bnodes[i], GADD(bnode_addrs[i], sizeof(GlobalAddress) + sizeof(BufferHeader)));
      else  index_cache->add_to_cache(leaves[slot_idx[i]].key,1,(InternalPage*)new_bnodes[i], GADD(bnode_addrs[i], sizeof(GlobalAddress) + sizeof(BufferHeader)));  //这里的k传错了 
      // assert(new_bnodes[i]->hdr.depth <7);
      // assert(ca_ptr->depth <7); 
    }*/
#endif
    old_e = new_entry;  //重新赋值 新增
    buffer_type_change = true;
    delete[] leaves;
    delete[] new_bnodes;
    delete[] node_pages;
    return true;

  }
  //old_e = *(InternalEntry*) cas_node_type_buffer;
      delete[] leaves;
    delete[] new_bnodes;
    delete[] node_pages;
  return false;

  }

}
//新建很多个缓冲节点 有重复的往里面放  
bool Tree::out_of_place_write_buffer_node_from_buffer(const Key &k, Value &v, int depth,InternalBuffer* bnode,int leaf_type,int klen,int vlen,GlobalAddress leaf_addr,CacheEntry**&entry_ptr_ptr,CacheEntry*& entry_ptr,bool from_cache,BufferEntry& old_e, GlobalAddress p_ptr,CoroContext *cxt, int coro_id) {
  return false;
}


bool Tree::insert_behind(const Key &k, Value &v, GlobalAddress p_ptr,int depth, GlobalAddress& leaf_addr, uint8_t partial_key, NodeType node_type,int leaf_type,int klen,int vlen,
                         const GlobalAddress &node_addr, uint64_t *ret_buffer, int& inserted_idx,
                         CoroContext *cxt, int coro_id) {
  int max_num, i;
  assert(node_type != NODE_256);
  max_num = node_type_to_num(node_type);
  // try cas an empty slot
  for (i = 0; i < 256 - max_num; ++ i) {
    auto slot_id = max_num + i;
    GlobalAddress e_ptr = GADD(node_addr, slot_id * sizeof(InternalEntry));
  //  auto cas_buffer = (dsm->get_rbuf(coro_id)).get_cas_buffer();
    //新建一个缓冲节点 和叶节点 一起写过去 最后cas
    GlobalAddress b_addr;
    b_addr = dsm->alloc(sizeof(InternalBuffer));

    auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaf_buffer();
    new (leaf_buffer) Leaf_kv(GADD(b_addr,sizeof(GlobalAddress)),leaf_type,klen,vlen,k, v);
    if(leaf_addr == GlobalAddress::Null())
    {    
    leaf_addr = dsm->alloc(sizeof(Leaf_kv));      
    }
    auto b_buffer=(dsm->get_rbuf(coro_id)).get_buffer_buffer();
   // if(GADD(node_addr, slot_id * sizeof(InternalEntry)).val == 0) printf("0001!\n");
    InternalBuffer* buffer = new (b_buffer) InternalBuffer(k,define::bPartialLenMax,depth +1 ,1,3,GADD(node_addr, slot_id * sizeof(InternalEntry)));  // 暂时定初始2B作为partial key buffer地址
    buffer->records[0] = BufferEntry(0,get_partial(k,depth+ buffer->hdr.partial_len +1),1,leaf_type,leaf_addr);

  
    auto new_e = InternalEntry(partial_key,1,b_addr);
    RdmaOpRegion *rs =  new RdmaOpRegion[2];
    {
      rs[0].source     = (uint64_t)b_buffer;
      rs[0].dest       = b_addr;
      rs[0].size       = sizeof(InternalBuffer);
      rs[0].is_on_chip = false;
    }
    {
        rs[1].source     = (uint64_t)leaf_buffer;
        rs[1].dest       = leaf_addr;
        rs[1].size       = sizeof(Leaf_kv);
        rs[1].is_on_chip = false;
    }
    dsm->write_batches_sync(rs, 2, cxt, coro_id);
    bool res = dsm->cas_sync(e_ptr, InternalEntry::Null(), (uint64_t)new_e, ret_buffer, cxt);  //可能这里cas不成功？？？
    delete[] rs; 

    if (res) {
      inserted_idx = slot_id;
#ifdef USE_CN_CACHE
        //加buffer到cacheindex_cache->add_to_cache(k, 1,(InternalPage *)buffer, GADD(b_addr, sizeof(GlobalAddress) + sizeof(BufferHeader)));
#endif
      return true;
    }
    // cas fail, check
    else {
      auto e = *(InternalEntry*) ret_buffer;   //按理说e不应该为空呀 
      if (e.partial == partial_key) {  // same partial keys insert to the same empty slot
        inserted_idx = slot_id;
        return false;  // search next level
      }
    }
    retry_cnt[dsm->getMyThreadID()][INSERT_BEHIND_TRY_NEXT] ++;
  }
  assert(false);
}

void avx_compare(void* p, char partial, std::vector<int>& v_k_i){
  BufferEntry* bp_node = (BufferEntry*) p;
  int k_i = 0;
    
  // 设置包含 'partial' 的 AVX-512 寄存器
  __m512i partial_vec = _mm512_set1_epi8(partial);

  for (; k_i <= 256 - 8; k_i += 8) {
      // 加载 64 个 BufferEntry 的第一个字节
      __m512i first_bytes = _mm512_maskz_loadu_epi8(0x101010101010101ULL, &bp_node[k_i].partial);

      // 比较第一个字节
      __mmask64 mask = _mm512_cmpeq_epi8_mask(partial_vec, first_bytes);

      // 将掩码转换为整数，检查哪些 BufferEntry 的 partial 字段匹配
      uint64_t mask64 = (uint64_t)mask;
      for (int i = 0; i < 8; ++i) {
        if ((mask64 & (1ULL << (i*8) )) && bp_node[k_i + i] != BufferEntry::Null()) {
          v_k_i.push_back(k_i + i);
        }
    }
  }

  // 处理剩余的元素
  for (; k_i < 256; ++k_i) {
    if (bp_node[k_i] != BufferEntry::Null() && bp_node[k_i].partial == partial) {
      v_k_i.push_back(k_i);
    }
    if (bp_node[k_i] == BufferEntry::Null()) {
      break;
    }
  }
}

bool Tree::search(const Key &k, Value &v, CoroContext *cxt, int coro_id) {   ///设置上限
#ifdef TEST_TIME
  auto start = std::chrono::high_resolution_clock::now();
#endif
  assert(dsm->is_register());
  int cnt_res=search_cnt_at.fetch_add(1);
  search_cnt[dsm->getMyThreadID()] ++;
  bool search_res = false;
  // traversal
  GlobalAddress p_ptr;
  InternalEntry p;
  BufferEntry bp;
  int depth;
  int retry_flag = FIRST_TRY;
  int leaf_type = -1;
  int parent_type = 0; //至上上层节点是internal node（0）还是internal buffer（1）
  uint64_t k_v;

  // cache
  bool from_cache = false;
  CacheEntry** entry_ptr_ptr = nullptr;
  CacheEntry* entry_ptr = nullptr;
  CacheEntry* cache_entry_parent = nullptr;
  CacheEntry** cache_entry_parent_ptr = nullptr;
  CacheEntry* cache_entry_buffer = nullptr;
  CacheEntry** cache_entry_buffer_ptr = nullptr;
  Key path;
  std::vector<InternalEntry> buffer_slot;

  int entry_idx = -1;
  int buffer_entry_idx = -1;
  int cache_depth = 0;

  // temp
  char* page_buffer;
  bool is_valid, type_correct;
  InternalPage* p_node = nullptr;
  InternalBuffer* bp_node = nullptr;
  InternalBuffer buffer_node;
  Header hdr;
  BufferHeader bhdr;
  int max_num;
  int parent_parent_type = 0;
  int buffer_from_cache_flag = 0;
  int first_buffer = 0;
#ifdef TEST_TIME
  auto search_from_cache_start = std::chrono::high_resolution_clock::now();
#endif
#ifdef USE_CN_CACHE
  from_cache = index_cache->search_from_cache(k, entry_ptr_ptr, entry_ptr, parent_parent_type,entry_idx,buffer_entry_idx,cache_entry_parent_ptr,cache_entry_parent,first_buffer);   //check   直接从cache里面找到一个 
  // if(entry_ptr->node_type == 1)
  //   assert(entry_idx < cache_entry_parent->records.size());
  // else
  //   assert(entry_idx < entry_ptr->records.size());
#ifdef TEST_TIME
  auto search_from_cache_stop = std::chrono::high_resolution_clock::now();
  auto search_from_cache_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(search_from_cache_stop - search_from_cache_start);  
  s_search_cache_time[dsm->getMyThreadID()] += search_from_cache_duration.count();
#endif
  if (from_cache) { // cache hit

    p_ptr = GADD(entry_ptr->addr, sizeof(InternalEntry) * entry_idx);
    p = entry_ptr->records[entry_idx];
    depth = entry_ptr->depth;
   // cache_depth = depth;
    parent_type  = entry_ptr->node_type;
    if(entry_ptr->node_type == 1)   //如果cache找到的缓冲节点则直接去读吧！！！  后面如果是从cache来的 并且类型就是一个缓冲节点就不用再读一遍了 还是再读一次吧、、、
    {
      cache_entry_buffer = entry_ptr;
      cache_entry_buffer_ptr = entry_ptr_ptr; 
      // depth = entry_ptr->depth;
      if(first_buffer)   //是第一个buffer 也就是位于第二层的buffer 并且这个buffer前面会有一个内部节点 这个时候cache就没有内部节点 所以没办法去失效
      {
        p_ptr = root_ptr_ptr;
        p = get_root_ptr(cxt, coro_id);
        parent_type = 0;
        depth = 1;
      }
      else{
        p_ptr = GADD(cache_entry_parent->addr,sizeof(InternalEntry)*entry_idx);
        p = cache_entry_parent->records[entry_idx];
        parent_type = cache_entry_parent->node_type;

        cache_entry_buffer = entry_ptr;
        cache_entry_buffer_ptr = entry_ptr_ptr; 
        depth =cache_entry_parent->depth;
        entry_ptr = cache_entry_parent;
        entry_ptr_ptr = cache_entry_parent_ptr;
        buffer_from_cache_flag = true;
      }

    }
    else
    {
      assert(entry_idx >= 0);
      cache_entry_parent = entry_ptr;
      cache_entry_parent_ptr = entry_ptr_ptr;
      // parent_page.hdr.depth = entry_ptr->depth;
    }     
    bp.val = p.val;
    if(!first_buffer) assert(cache_entry_parent !=0);  //只要是从cache拿到的一定会拿到一个父节点  不见得不见得 如果是深度为2的buffer
  }
  else {
        p_ptr = root_ptr_ptr;
    p = get_root_ptr(cxt, coro_id);
    depth = 0;
  }
      // if(buffer_from_cache_flag) bufffer_from_cache_cnt[dsm->getMyThreadID()] ++;
#else
    p_ptr = root_ptr_ptr;
    p = get_root_ptr(cxt, coro_id);
    depth = 0;
#endif

  path[depth] = p.partial;
  depth ++;
  cache_depth = depth;
  assert(p != InternalEntry::Null());
  k_v = key2int(k);
next:
  retry_cnt[dsm->getMyThreadID()][retry_flag] ++;
  // 1. If we are at a NULL node

  // parent_type = 0;
  if(parent_type == 0)   //一个内部节点 顺着往下找
  {
  if (p == InternalEntry::Null()) {
    assert(from_cache == false);
    search_res = false;
    goto search_finish;
  }

  // 2. If we are at a buffer, read the buffer
  if (p.child_type == 1) {

    auto buffer_buffer =  (dsm->get_rbuf(coro_id)).get_buffer_buffer();
    bool buffer_res = false;
    bool flag_atc = false;

    if(buffer_from_cache_flag)
     {
      buffer_slot = cache_entry_buffer->records;
      bp_node = &buffer_node;
      bp_node->hdr.depth = depth;
      bp_node->rev_ptr = p_ptr;
      bp_node->lock_byte = 0;
      bufffer_from_cache_cnt[dsm->getMyThreadID()] ++;
     }
     else{
read_buffer:
#ifdef TEST_TIME
      auto read_buffer_start = std::chrono::high_resolution_clock::now();
#endif
      // auto read_buffer_node_start = std::chrono::high_resolution_clock::now();
      read_buffer_node(p.addr(), buffer_buffer, p_ptr, depth, buffer_from_cache_flag,cxt, coro_id);

      // auto read_buffer_node_stop = std::chrono::high_resolution_clock::now();
      // auto read_buffer_node_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(read_buffer_node_stop - read_buffer_node_start);  
      // read_buffer_node_time[0][dsm->getMyThreadID()] += read_buffer_node_duration.count();  
#ifdef TEST_TIME
      auto read_buffer_stop = std::chrono::high_resolution_clock::now();
      auto read_buffer_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(read_buffer_stop - read_buffer_start);  
      search_read_buffer_time[dsm->getMyThreadID()] += read_buffer_duration.count();
#endif      
      bp_node = (InternalBuffer *)buffer_buffer;
      is_valid =    bp_node->hdr.depth <= depth && (!buffer_from_cache_flag || bp_node->rev_ptr == p_ptr);
      if (!is_valid) {  // node deleted || outdated cache entry in cached node
#ifdef USE_CN_CACHE
        if (buffer_from_cache_flag) {
          // index_cache->invalidate(entry_ptr_ptr, entry_ptr); //invalid 父节点 父节点其实没有必要失效吧
          index_cache->invalidate(cache_entry_buffer_ptr, cache_entry_buffer); //invalid 缓冲节点
        }
#endif
        // re-read node entry
        auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
        dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
        p = *(InternalEntry *)entry_buffer;
        from_cache = false;
        buffer_from_cache_flag = false;
        retry_flag = INVALID_Buffer_NODE;
        goto next;
      }


    }
      bhdr=bp_node->hdr;
    //2.1 check partial key
    if(!buffer_from_cache_flag)
    {

#ifdef USE_CN_CACHE
#ifdef TEST_TIME
        auto cache_op_start = std::chrono::high_resolution_clock::now();
#endif
      if (depth == bhdr.depth && !buffer_from_cache_flag) {
        flag_atc = true;
      // index_cache->add_to_cache(k, 1,(InternalPage*)bp_node, GADD(p.addr(), sizeof(GlobalAddress)));
      }
#ifdef TEST_TIME
        auto cache_op_stop = std::chrono::high_resolution_clock::now();
  auto cache_op_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(cache_op_stop - cache_op_start);  
  cache_ops_time[dsm->getMyThreadID()] += cache_op_duration.count();
#endif
#endif

/*      for (int i = 0; i < bhdr.partial_len; ++ i) {      //查看部分键前n个字节
      if (get_partial(k, bhdr.depth + i) != bhdr.partial[i]) {
        search_res = false;
        goto search_finish;
      }
      }*/
      depth = bhdr.depth + bhdr.partial_len ;
      if(bp_node->lock_byte == 99) 
        {
          p_node = (InternalPage*)bp_node;
          // from_cache = false;
          buffer_from_cache_flag = false;
          goto internal_node;
        }
    }
    
  //  uint16_t fp = generateFingerprint(k);

    //2.2 if all partial key match search from the start else from the end 
//    if(get_partial(k, bhdr.depth + bhdr.partial_len -1 ) == bhdr.partial[bhdr.partial_len -1 ] )
//    {
      std::vector<int> v_k_i;
      v_k_i.reserve(32);
      if(buffer_from_cache_flag){
        std::memcpy(bp_node->records, buffer_slot.data(), buffer_slot.size() * sizeof(uint64_t));
        // bp_node->records[k_i].val = buffer_slot[k_i].val;
      }
#ifdef TEST_TIME
      auto search_buffer_loop_start = std::chrono::high_resolution_clock::now();
#endif
      int leaf_cnt = 0;

            //      auto buffer_buffer1 =  (dsm->get_rbuf(coro_id)).get_buffer_buffer();
            //  read_buffer_node(p.addr(), buffer_buffer1,0, depth, true,cxt, coro_id);

      uint8_t partial = get_partial(k, bhdr.depth + bhdr.partial_len);
      int k_i = 0;
#ifdef AVX_ACC
      avx_compare(bp_node->records,partial,v_k_i);
#else
      for(; k_i < 256 ;k_i++)
      {
      if(buffer_from_cache_flag){
            bp_node->records[k_i].val = buffer_slot[k_i].val;
          }
      if(bp_node->records[k_i] == BufferEntry::Null() || (buffer_from_cache_flag && k_i == buffer_slot.size()))
        break;
      if(bp_node->records[k_i] != BufferEntry::Null()&&bp_node->records[k_i].partial == partial )
      {
        assert(bp_node->records[k_i].addr().nodeID == 0);
        if(bp_node->records[k_i].node_type == 1 || bp_node->records[k_i].node_type == 2)   //是一个缓冲节点 或者内部节点 继续往下找 
        {
          // bp = bp_node->records[k_i];
          p = *(InternalEntry*)&(bp_node->records[k_i]);
          p_ptr = GADD(p.addr(), sizeof(GlobalAddress) + k_i*sizeof(BufferEntry));
          depth ++;
          parent_type = 0;  //代表是一个内部节点
          from_cache = false;
          buffer_from_cache_flag = false;
          retry_flag = FIND_NEXT;
          goto next;
        }
        else 
        {
          leaf_addrs[coro_id][leaf_cnt] = bp_node->records[k_i].addr();
          assert(bp_node->records[k_i].addr().val !=0);
          leaves_ptr[coro_id][leaf_cnt]  = GADD(p.addr(), sizeof(GlobalAddress) + k_i*sizeof(BufferEntry));
          leaf_cnt ++;   
        }
        v_k_i.push_back(k_i);
      }

      }
#endif
      buffer_empty_slot[dsm->getMyThreadID()] +=v_k_i.size()*1.0/256;
      buffer_cnt_all[dsm->getMyThreadID()]++;

#ifdef TEST_TIME
      auto search_buffer_loop_stop = std::chrono::high_resolution_clock::now();
      auto search_buffer_loop_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(search_buffer_loop_stop - search_buffer_loop_start);  
      buffer_loop[dsm->getMyThreadID()] += search_buffer_loop_duration.count();
#endif
      for(int i = 0; i < v_k_i.size(); i++){
        int kk_i = v_k_i[i];
        leaf_addrs[coro_id][leaf_cnt] = bp_node->records[kk_i].addr();
        leaves_ptr[coro_id][leaf_cnt]  = GADD(p.addr(), sizeof(GlobalAddress) + kk_i*sizeof(BufferEntry));
        leaf_cnt ++;
      }
      if(leaf_cnt == 0)
      {
        if(buffer_from_cache_flag)
        {
          buffer_from_cache_flag = false;
          goto read_buffer;
        }
        search_res = false;
        goto search_finish;
      }
      if(!buffer_from_cache_flag && flag_atc)
      {
        #ifdef USE_CN_CACHE
#ifdef TEST_TIME
        auto cache_op_start = std::chrono::high_resolution_clock::now();
#endif
      if (depth == bhdr.depth && !buffer_from_cache_flag) {
        // flag_atc = true;
            // printf("thread  %d 18 node value is %" PRIu64" \n",(int)dsm->getMyThreadID( ),(uint64_t)(bp_node->hdr));
      index_cache->add_to_cache(k, 1,(InternalPage*)bp_node, GADD(p.addr(), sizeof(GlobalAddress) ));
      }
#ifdef TEST_TIME
        auto cache_op_stop = std::chrono::high_resolution_clock::now();
  auto cache_op_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(cache_op_stop - cache_op_start);  
  cache_ops_time[dsm->getMyThreadID()] += cache_op_duration.count();
#endif
#endif
      }      

      //read_batch 都读过来检查 
#ifdef TEST_TIME
      auto search_read_leaves_start = std::chrono::high_resolution_clock::now();
#endif
      auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_range_buffer(); 
      is_valid = read_small_leaves(leaf_addrs[coro_id], leaf_buffer,leaf_cnt,leaves_ptr[coro_id],buffer_from_cache_flag,cxt,coro_id);
#ifdef TEST_TIME
      auto search_read_leaves_stop = std::chrono::high_resolution_clock::now();
      auto search_read_leaves_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(search_read_leaves_stop - search_read_leaves_start);  
      search_read_leaf_time[dsm->getMyThreadID()] += search_read_leaves_duration.count();
#endif
    // if(0) {
    if (!is_valid) {
      // re-read internal entry
#ifdef USE_CN_CACHE
      if (from_cache) {
        // index_cache->invalidate(cache_entry_buffer_ptr, cache_entry_buffer);  其实是没必要失效的？
      }
#endif
      auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
      dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
      p = *(InternalEntry *)entry_buffer;
      from_cache = false;
      retry_flag = INVALID_LEAF;
      goto next;
    }
    for(int i =0;i<leaf_cnt;i++)
    {
      auto leaf = (Leaf_kv*) leaf_buffer + i* define::allocAlignKVLeafSize;
      auto _k = leaf->get_key();
      bool res = _k==k;

      // 2.3 Check if it is the key we search
      if (res) {
        v = leaf->get_value();
        search_buffer_cache_true[dsm->getMyThreadID()] ++;
        search_res = true;
      goto search_finish;
      }

    }
    if(buffer_from_cache_flag)
    {
      buffer_from_cache_flag = false;
      goto read_buffer;
    }
    search_res = false;
    goto search_finish;

    }

  // 3. Find out a node
  // 3.1 read the node
// if(p.child_type == 2)
{
  {
#ifdef TEST_TIME
      auto read_internal_start = std::chrono::high_resolution_clock::now();
#endif
  page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
  is_valid = read_node(p, type_correct, page_buffer, p_ptr, depth, from_cache,cxt, coro_id);
  p_node = (InternalPage *)page_buffer;
#ifdef TEST_TIME
      auto read_internal_stop = std::chrono::high_resolution_clock::now();
      auto read_internal_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(read_internal_stop - read_internal_start);  
      search_read_internal_time[dsm->getMyThreadID()] += read_internal_duration.count();
#endif    
}



  if (!is_valid) {  // node deleted || outdated cache entry in cached node
    // re-read node entry
#ifdef USE_CN_CACHE
    if (from_cache) {
      index_cache->invalidate(entry_ptr_ptr, entry_ptr);
    }
#endif
    auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
    dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
    p = *(InternalEntry *)entry_buffer;
    from_cache = false;
    retry_flag = INVALID_Internal_NODE;
    goto next;
  }

internal_node:
  // 3.2 Check header
  hdr = p_node->hdr;
#ifdef USE_CN_CACHE  
  if (depth == hdr.depth) {
    index_cache->add_to_cache(k,0,p_node, GADD(p.addr(), sizeof(GlobalAddress)));
  }
#endif

  for (int i = 0; i < hdr.partial_len; ++ i) {
    if (get_partial(k, hdr.depth + i) != hdr.partial[i]) {
      search_res = false;
      goto search_finish;
    }
  }
  for(int i = depth;i<hdr.depth + hdr.partial_len;i++) path[i] = hdr.partial[i-depth];  
  depth = hdr.depth + hdr.partial_len;

  // 3.3 try get the next internalEntry
  // max_num = node_type_to_num(p.type());
  max_num = 256;
  // find from the exist slot
  for (int i = 0; i < max_num; ++ i) {
    auto old_e = p_node->records[i];
    if (old_e != InternalEntry::Null() && old_e.partial == get_partial(k, hdr.depth + hdr.partial_len)) {
      p_ptr = GADD(p.addr(), sizeof(GlobalAddress) + i * sizeof(InternalEntry));
      p = old_e;
      parent_type = 0;
      path[depth] = p.partial;
      depth ++;
      from_cache = false;    
      buffer_from_cache_flag = false;  
      retry_flag = FIND_NEXT;
      goto next;  // search next level
    }
    if(old_e == InternalEntry::Null()) break;
  }
  //在内部节点里面没找到  但是这个内部节点也要加cache  已经加了
}
}
else{   //parent是一个buffernode
  if (bp == BufferEntry::Null()) {
    search_res = false;
    goto search_finish;
  }

  // 2. If we are at a buffer, read the buffer
  if (bp.node_type == 1) {

    auto buffer_buffer =  (dsm->get_rbuf(coro_id)).get_buffer_buffer();
    is_valid = read_buffer_node(bp.addr(), buffer_buffer, p_ptr, depth,from_cache, cxt, coro_id);
    bp_node = (InternalBuffer *)buffer_buffer;
    if (!is_valid) {  // node deleted || outdated cache entry in cached node
    // invalidate the old node cache
    if (from_cache) {
      index_cache->invalidate(entry_ptr_ptr, entry_ptr);
    }
    // re-read node entry
    auto entry_buffer = (dsm->get_rbuf(coro_id)).get_buffer_entry_buffer();
    dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(BufferEntry), cxt);
    bp = *(BufferEntry *)entry_buffer;
    from_cache = false;
    retry_flag = INVALID_Buffer_NODE;
    goto next;
  }
    //2.1 check partial key
    bhdr=bp_node->hdr;

    for (int i = 0; i < bhdr.partial_len; ++ i) {      //查看部分键前n个字节
    if (get_partial(k, bhdr.depth + i) != bhdr.partial[i]) {
      search_res = false;
      goto search_finish;
    }
    }
    depth = bhdr.depth + bhdr.partial_len;
  //  uint16_t fp = generateFingerprint(k);

    //2.2 if all partial key match search from the start else from the end 
//    if(get_partial(k, bhdr.depth + bhdr.partial_len -1 ) == bhdr.partial[bhdr.partial_len -1 ] )
//    {
      int leaf_cnt = 0;
      GlobalAddress leaf_addrs[256];
      GlobalAddress leaves_ptr[256];

      uint8_t partial = get_partial(k, bhdr.depth + bhdr.partial_len);
      for(int i =0 ; i < 256 ;i++)
      {
        BufferEntry b_e;
        if(buffer_from_cache_flag){
          bp_node->records[i].val = cache_entry_buffer->records[i].val;
        }
        b_e.val = bp_node->records[i].val;
      if(b_e != BufferEntry::Null() && b_e.partial == partial )
      {
      //  assert(bp_node->records[i].addr().nodeID == 0);
          leaf_addrs[leaf_cnt] = b_e.addr();
          leaves_ptr[leaf_cnt]  = GADD(p.addr(), sizeof(GlobalAddress) + i*sizeof(BufferEntry));
          leaf_cnt ++;
      }
      if(b_e == BufferEntry::Null())
        break; // 找到空的就直接break
      }
      if(leaf_cnt == 0)
      {
        search_res = false;
        goto search_finish;
      }
    //2.3 kv leaf
     auto leaf_buffer = (dsm->get_rbuf(coro_id)).get_kvleaves_buffer(leaf_cnt); 

    
    is_valid = read_leaves(leaf_addrs, leaf_buffer,leaf_cnt,leaves_ptr,from_cache,cxt,coro_id);

    if (!is_valid) {
      if (from_cache) {
        index_cache->invalidate(entry_ptr_ptr, entry_ptr);
      }
      auto entry_buffer = (dsm->get_rbuf(coro_id)).get_buffer_entry_buffer();
      dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(BufferEntry), cxt);
      bp = *(BufferEntry *)entry_buffer;
      retry_flag = INVALID_LEAF;
      goto next;
    }
    for(int i =0;i<leaf_cnt;i++)
    {
      auto leaf = (Leaf_kv*) leaf_buffer + i* define::allocAlignKVLeafSize;
      auto _k = leaf->get_key();

      // 2.3 Check if it is the key we search
      if (_k == k) {
        v = leaf->get_value();
        search_res = true;
      }
      goto search_finish;
    }
    return false;
  }

  // 3. Find out a node
  // 3.1 read the node
  page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
  is_valid = read_node_from_buffer(bp, type_correct, page_buffer, p_ptr, depth, from_cache,cxt, coro_id);
  p_node = (InternalPage *)page_buffer;

  if (!is_valid) {  // node deleted || outdated cache entry in cached node
    if (from_cache) {
      index_cache->invalidate(entry_ptr_ptr, entry_ptr);
    }
    // re-read node entry

    auto entry_buffer = (dsm->get_rbuf(coro_id)).get_buffer_entry_buffer();
    dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(BufferEntry), cxt);
    bp = *(BufferEntry *)entry_buffer;
    from_cache = false;
    retry_flag = INVALID_Internal_NODE;
    goto next;
  }

  // 3.2 Check header
  hdr = p_node->hdr;
  // if (depth == hdr.depth) {
    // index_cache->add_to_cache(k,0,p_node, GADD(bp.addr(), sizeof(GlobalAddress) + sizeof(BufferHeader)));
  // }

  for (int i = 0; i < hdr.partial_len; ++ i) {
    if (get_partial(k, hdr.depth + i) != hdr.partial[i]) {
      search_res = false;
      goto search_finish;
    }
  }
  depth = hdr.depth + hdr.partial_len;

  // 3.3 try get the next internalEntry
  max_num = node_type_to_num(p.type());
  // find from the exist slot
  for (int i = 0; i < max_num; ++ i) {
    auto old_e = p_node->records[i];
    if (old_e != InternalEntry::Null() && old_e.partial == get_partial(k, hdr.depth + hdr.partial_len)) {
      p_ptr = GADD(bp.addr(), sizeof(GlobalAddress) + i * sizeof(InternalEntry));
      p = old_e;
      depth ++;
      parent_type = 0;
      from_cache = false;
      retry_flag = FIND_NEXT;
      goto next;  // search next level
    }
  }

  }
search_finish:
#ifdef TEST_TIME
  auto stop = std::chrono::high_resolution_clock::now();
  auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(stop - start);  
  search_time[dsm->getMyThreadID()] += duration.count();
#endif

    auto hit = (cache_depth == 1 ? 0 : (double)cache_depth / depth);
    cache_hit[dsm->getMyThreadID()] += hit;
    cache_miss[dsm->getMyThreadID()] += (1 - hit);
  return search_res;
}


/*
void Tree::search_entries(const Key &from, const Key &to, int target_depth, std::vector<ScanContext> &res, CoroContext *cxt, int coro_id) {
  assert(dsm->is_register());

  GlobalAddress p_ptr;
  InternalEntry p;
  int depth;
  bool from_cache = false;
  volatile CacheEntry** entry_ptr_ptr = nullptr;
  CacheEntry* entry_ptr = nullptr;
  int entry_idx = -1;
  int cache_depth = 0;

  bool type_correct;
  char* page_buffer;
  bool is_valid;
  InternalPage* p_node;
  Header hdr;
  int max_num;

  // search local cache
#ifdef TREE_ENABLE_CACHE
  from_cache = index_cache->search_from_cache(from, entry_ptr_ptr, entry_ptr, entry_idx);
  if (from_cache) { // cache hit
    assert(entry_idx >= 0);
    p_ptr = GADD(entry_ptr->addr, sizeof(InternalEntry) * entry_idx);
    p = entry_ptr->records[entry_idx];
    depth = entry_ptr->depth;
  }
  else {
    p_ptr = root_ptr_ptr;
    p = get_root_ptr(cxt, coro_id);
    depth = 0;
  }
#else
  p_ptr = root_ptr_ptr;
  p = get_root_ptr(cxt, coro_id);
  depth = 0;
#endif
  depth ++;
  cache_depth = depth;

next:
  // 1. If we are at a NULL node
  if (p == InternalEntry::Null()) {
    goto search_finish;
  }

  // 2. Check if it is the target depth
  if (depth == target_depth) {
    res.push_back(ScanContext(p, p_ptr, depth-1, from_cache, entry_ptr_ptr, entry_ptr, from, to, BORDER, BORDER));
    goto search_finish;
  }
  if (p.is_leaf) {
    goto search_finish;
  }

  // 3. Find out a node
  // 3.1 read the node
  page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
  is_valid = read_node(p, type_correct, page_buffer, p_ptr, depth, from_cache, cxt, coro_id);
  p_node = (InternalPage *)page_buffer;

  if (!is_valid) {  // node deleted || outdated cache entry in cached node
#ifdef TREE_ENABLE_CACHE
    // invalidate the old node cache
    if (from_cache) {
      index_cache->invalidate(entry_ptr_ptr, entry_ptr);
    }
#endif
    // re-read node entry
    auto entry_buffer = (dsm->get_rbuf(coro_id)).get_entry_buffer();
    dsm->read_sync((char *)entry_buffer, p_ptr, sizeof(InternalEntry), cxt);
    p = *(InternalEntry *)entry_buffer;
    from_cache = false;
    goto next;
  }

  // 3.2 Check header
  hdr = p_node->hdr;
#ifdef TREE_ENABLE_CACHE
  if (from_cache && !type_correct) {
    index_cache->invalidate(entry_ptr_ptr, entry_ptr);  // invalidate the out dated node type
  }
#else
  UNUSED(type_correct);
#endif
  for (int i = 0; i < hdr.partial_len; ++ i) {
    if (get_partial(from, hdr.depth + i) != hdr.partial[i]) {
      goto search_finish;
    }
    if (hdr.depth + i + 1 == target_depth) {
      range_query_on_page(p_node, from_cache, depth-1,
                          p_ptr, p,
                          from, to, BORDER, BORDER, res);
      goto search_finish;
    }
  }
  depth = hdr.depth + hdr.partial_len;

  // 3.3 try get the next internalEntry
  // find from the exist slot
  max_num = node_type_to_num(p.type());
  for (int i = 0; i < max_num; ++ i) {
    auto old_e = p_node->records[i];
    if (old_e != InternalEntry::Null() && old_e.partial == get_partial(from, hdr.depth + hdr.partial_len)) {
      p_ptr = GADD(p.addr(), sizeof(GlobalAddress) + sizeof(Header) + i * sizeof(InternalEntry));
      p = old_e;
      from_cache = false;
      depth ++;
      goto next;  // search next level
    }
  }
search_finish:
#ifdef TREE_ENABLE_CACHE
  auto hit = (cache_depth == 1 ? 0 : (double)cache_depth / depth);
  cache_hit[dsm->getMyThreadID()] += hit;
  cache_miss[dsm->getMyThreadID()] += (1 - hit);
#endif
  return;
}
*/
/*
  range query, DO NOT support corotine currently
*/
// [from, to)
/**/
void Tree::range_query(const Key &from, const Key &to, std::map<Key, Value> &ret) {

}


void Tree::range_query_on_page(InternalPage* page, bool from_cache, int depth,
                               GlobalAddress p_ptr, InternalEntry p,
                               const Key &from, const Key &to, State l_state, State r_state,
                               std::vector<ScanContext>& res) {

}


void Tree::run_coroutine(GenFunc gen_func, WorkFunc work_func, int coro_cnt, Request* req, int req_num) {
  using namespace std::placeholders;

  assert(coro_cnt <= MAX_CORO_NUM);
  for (int i = 0; i < coro_cnt; ++i) {
    RequstGen *gen = gen_func(dsm, req, req_num, i, coro_cnt);
    worker[i] = CoroCall(std::bind(&Tree::coro_worker, this, _1, gen, work_func, i));
  }

  master = CoroCall(std::bind(&Tree::coro_master, this, _1, coro_cnt));

  master();
}


void Tree::coro_worker(CoroYield &yield, RequstGen *gen, WorkFunc work_func, int coro_id) {
  CoroContext ctx;
  ctx.coro_id = coro_id;
  ctx.master = &master;
  ctx.yield = &yield;

  Timer coro_timer;
  auto thread_id = dsm->getMyThreadID();

  while (!need_stop) {
  // uint64_t end_warm_key = 0.2 * 60 * define::MB;
  // for (uint64_t i = 1; i < end_warm_key; ++i) {  //线程多起来之后会更加分散
    auto r = gen->next();
    // auto r = gen->next(i);
    coro_timer.begin();
    work_func(this, r, &ctx, coro_id);
    auto us_10 = coro_timer.end() / 100;

    if (us_10 >= LATENCY_WINDOWS) {
      us_10 = LATENCY_WINDOWS - 1;
    }
    latency[thread_id][coro_id][us_10]++;
    // if(need_stop) break;
  }
}


void Tree::coro_master(CoroYield &yield, int coro_cnt) {
  for (int i = 0; i < coro_cnt; ++i) {
    yield(worker[i]);
  }
  while (!need_stop) {
    uint64_t next_coro_id;

    if (dsm->poll_rdma_cq_once(next_coro_id)) {
      yield(worker[next_coro_id]);
    }
    // uint64_t wr_ids[POLL_CQ_MAX_CNT_ONCE];
    // int cnt = dsm->poll_rdma_cq_batch_once(wr_ids, POLL_CQ_MAX_CNT_ONCE);
    // for (int i = 0; i < cnt; ++ i) {
    //   yield(worker[wr_ids[i]]);
    // }

    if (!busy_waiting_queue.empty()) {
    // int cnt = busy_waiting_queue.size();
    // while (cnt --) {
      auto next = busy_waiting_queue.front();
      busy_waiting_queue.pop();
      next_coro_id = next.first;
      if (next.second()) {
        yield(worker[next_coro_id]);
      }
      else {
        busy_waiting_queue.push(next);
      }
    }
  }
}


void Tree::statistics() {
#ifdef USE_CN_CACHE
  index_cache->statistics();
#endif
}

void Tree::clear_debug_info() {
  memset(cache_miss, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(cache_hit, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(lock_fail, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  // memset(try_lock, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(write_handover_num, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(try_write_op, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(read_handover_num, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(try_read_op, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(read_leaf_retry, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(leaf_cache_invalid, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(try_read_leaf, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(read_node_repair, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(try_read_node, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(read_node_type, 0, sizeof(uint64_t) * MAX_APP_THREAD * MAX_NODE_TYPE_NUM);
  memset(retry_cnt, 0, sizeof(uint64_t) * MAX_APP_THREAD * MAX_FLAG_NUM);
  memset(insert_type,-1,sizeof(int)*MAX_APP_THREAD);
  memset(insert_cnt,0,8*sizeof(uint64_t)*MAX_APP_THREAD);
  memset(internal_empty_entry,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(internal_extend_empty_entry,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(internal_header_split,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(buffer_empty_entry,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(buffer_header_split,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(buffer_reconstruct,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(in_place_update,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(insert_time,0,sizeof(uint64_t)*MAX_APP_THREAD*8);
  memset(search_from_cache_time,0,sizeof(uint64_t)*MAX_APP_THREAD*8);
  memset(read_buffer_node_time,0,sizeof(uint64_t)*MAX_APP_THREAD*8);
  memset(read_internal_node_time,0,sizeof(uint64_t)*MAX_APP_THREAD*8);
  memset(read_leaves_time,0,sizeof(uint64_t)*MAX_APP_THREAD*8);
  memset(bufffer_from_cache_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(buffer_empty_loop_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(buffer_empty_loop_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(search_cache_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);   
  memset(read_buffer_node_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);   
  memset(read_internal_node_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);   
  memset(internal_slot_loop_time,0,sizeof(uint64_t)*MAX_APP_THREAD);   
  memset(internal_slot_loop_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);  
  memset(dur,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(cp_buffer_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(cp_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(buffer_node_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(internal_node_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD * 8);
  memset(search_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(search_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(s_search_cache_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(search_read_buffer_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(search_read_internal_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(search_read_leaf_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(cache_ops_time,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(buffer_loop,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(bufffer_from_cache_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(search_buffer_cache_true,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(buffer_empty_slot,0,sizeof(double)*MAX_APP_THREAD);
  memset(buffer_cnt_all,0,sizeof(uint64_t)*MAX_APP_THREAD);
  memset(bufffer_from_cache_cnt,0,sizeof(uint64_t)*MAX_APP_THREAD);
}
