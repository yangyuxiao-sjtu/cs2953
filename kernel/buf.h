struct buf {
  uchar data[BSIZE];
  int valid;   // has data been read from disk?
  int disk;    // does disk "own" buf?
  uint dev;
  uint blockno;
  struct sleeplock lock;
  uint refcnt;
  struct buf *prev; // LRU cache list
  struct buf *next;
  int ismmaped;
}__attribute__((aligned(4096)));;

