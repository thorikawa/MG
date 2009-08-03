#include <stdio.h>
#include <string>
#include <map>
#include <vector>
#include <deque>
#include <unistd.h>
#include <inttypes.h>

#define BUFFER_SIZE 256
#define MODEL_BRAID 0
#define MODEL_BYTE 1

using namespace std;
typedef unsigned char byte, uchar;
typedef unsigned int uint;
typedef unsigned long ulong;

class State {
public:
  State (uint id) : id(id) {
  }
  ~State () {
    next_state.clear();
    trans_count.clear();
  }
  int GetId () {
    return id;
  }
  void SetNextState (uchar input, State *state) {
    next_state[input] = state;
  }
  State* GetNextState (uchar input) {
    return next_state[input];
  }
  void SetTransCount (uchar input, uint count) {
    trans_count[input] = count;
  }
  uint GetTransCount (uchar input) {
    return trans_count[input];
  }
  uint GetTotalCount () {
    uint total = 0;
    map<uchar, uint>::iterator it = trans_count.begin();
    while (it != trans_count.end()) {
      total += (*it).second;
      ++it;
    }
    return total;
  }
private:
  uint id;
  map<uchar, State*> next_state;
  map<uchar, uint> trans_count;
};
// Dynamic Markov compressionのベースクラス
class DmcBase {
public:
  DmcBase (int model) {
    Init(model);
  }
  ~DmcBase () {}
  void SetFilePointer (FILE *outfp) {
    outfp_ = outfp;
  }
  void SetCloningThreshold1 (uint cloning_threshold1) {
    cloning_threshold1_ = cloning_threshold1;
  }
  void SetCloningThreshold2 (uint cloning_threshold2) {
    cloning_threshold2_ = cloning_threshold2;
  }
  ulong GetCloningCount () {
    return cloning_count_;
  }
  ulong GetStateCount () {
    return last_state_+1;
  }
protected:
  // 分離点(mp)を計算する。
  ulong CalculateMP () {
    double p0, p1;
    ulong mp;
    uint totalCount = current_state_->GetTotalCount();
    p0 = (double) (current_state_->GetTransCount(0) + 1) / (totalCount + 2);
    p1 = (double) (current_state_->GetTransCount(1) + 1) / (totalCount + 2);
    mp = (ulong) ((p1 * lower_bound_ + p0 * upper_bound_) / (p0 + p1));
    if (mp <= lower_bound_) {
      mp = lower_bound_ + 1;
    }
    // mpの最右bitを1に変更
    mp = mp | 1;
    // 最右bitを1に変更した結果、upper_bound_を超える可能性がある。その場合、mp=upper_bound_とする。
    if (mp > upper_bound_) {
      mp = upper_bound_;
    }
    return mp;
  }
  // 出力バッファに引数として指定されたbitを格納する。
  void AddBuffer (uchar outbit) {
    temp_ = temp_ + (outbit << bit_count_);
    if (++bit_count_ == 8) {
      buffer_[buffer_count_++] = temp_;
      temp_ = 0;
      bit_count_ = 0;
      for (unsigned int i=0; i<buffer_count_; i++) {
        fputc(*(buffer_+i), outfp_);
      }
      buffer_count_ = 0;
    }
  }
  // クローニングを行う。
  void DoCloning (uchar bit) {
    uint trans_count = current_state_->GetTransCount(bit);
    State *next_state = current_state_->GetNextState(bit);
    uint next_count = next_state->GetTotalCount();
    
    if (trans_count > cloning_threshold1_ && (next_count - trans_count) > cloning_threshold2_) {
      State *new_state = new State(last_state_++);
      current_state_->SetNextState(bit, new_state);
      double ratio = (double) (trans_count + 1) / (next_count + 2);
      // ratioの正規化(CloningはCloning後の次状態のtrans_count <= 現状態のtrans_countを保証していないので、ratioが1を超える場合がある。
      if (ratio > 1) {
        ratio = 1;
      }
      for (int i=0; i<=1; i++) {
        uint next_count_bit = next_state->GetTransCount(i);
        uint new_next_count_bit = (uint)(ratio * next_count_bit);
        new_state->SetNextState(i, next_state->GetNextState(i));
        new_state->SetTransCount(i, new_next_count_bit);
        next_state->SetTransCount(i, next_count_bit - new_next_count_bit);
      }
      cloning_count_++;
    }
  }
  // メンバ変数・マルコフ連鎖の初期化を行う。
  void Init (int model) {
    last_state_ = 0;
    if (model == MODEL_BYTE) {
      InitStatesWithByteModel();
    } else {
      InitStatesWithBraid ();
    }
    lower_bound_ = 0;
    upper_bound_ = kMSMASK;
    buffer_count_ = 0;
    bit_count_ = 0;
    temp_ = 0;
    cloning_count_ = 0;
    cloning_threshold1_ = 16;
    cloning_threshold2_ = 16;
  }
  // マルコフ連鎖をBraid構造で初期化する。
  void InitStatesWithBraid () {
    for (uint i=0; i<kNBITS; i++) {
      for (uint j=0; j<kSTRANDS; j++) {
        State *state = new State(last_state_++);
        state->SetTransCount(0,0);
        state->SetTransCount(1,0);
        state_map_[i+kNBITS*j] = state;
      }
    }
    for (uint i=0; i<kNBITS; i++) {
      for (uint j=0; j<kSTRANDS; j++) {
        uint k = (i+1) % kNBITS;
        State *state = state_map_[i+kNBITS*j];
        state->SetNextState(0, state_map_[k + (( 2*j ) % kSTRANDS) * kNBITS]);
        state->SetNextState(1, state_map_[k + (( 2*j + 1 ) % kSTRANDS) * kNBITS]);
      }
    }
    current_state_ = state_map_[0];
  }
  // マルコフ連鎖をByte構造で初期化する。
  void InitStatesWithByteModel () {
    State *state = new State(last_state_++);
    state->SetTransCount(0,0);
    state->SetTransCount(1,0);
    state_map_[state->GetId()] = state;
    InitStatesWithByteModel(state, 0);
    current_state_ = state;
  }
  // マルコフ連鎖をByte構造で初期化する。（再帰呼び出し用関数）
  void InitStatesWithByteModel (State *parent, int depth) {
    if (depth < 7) {
      for (int i=0; i<2; i++) {
        State *state = new State(last_state_++);
        state->SetTransCount(0,0);
        state->SetTransCount(1,0);
        parent->SetNextState(i, state);
        InitStatesWithByteModel(state, depth+1);
        state_map_[state->GetId()] = state;
      }
    } else {
      for (int i=0; i<2; i++) {
        parent->SetNextState(i, state_map_[0]);
      }
    }
  }
  static const uint kNBITS = 8;
  static const uint kSTRANDS = 256;
  static const int kN = 31;
  static const ulong kMSBIT = 1 << (kN-1);
  static const ulong kMSMASK = (1 << kN) - 1 ;
  map<uint, State*> state_map_;
  FILE *outfp_;
  ulong lower_bound_;
  ulong upper_bound_;
  vector<State*> state_vec_;
  State *current_state_;
  ulong last_state_;
  byte buffer_[BUFFER_SIZE];
  uint buffer_count_;
  byte temp_;
  uchar bit_count_;
  ulong cloning_count_;
  uint cloning_threshold1_;
  uint cloning_threshold2_;

};
// Dynamic Markov compressionのエンコーダクラス
class DmcEncoder : public DmcBase {
public:
  DmcEncoder (int model) : DmcBase (model) {
  }
  void Encode (uchar bit) {
    ulong mp = CalculateMP();
    Encode(bit, mp);
  }
  void Encode (uchar bit, ulong mp) {
    if (bit == 1) {
      lower_bound_ = mp;
    } else {
      upper_bound_ = mp - 1;
    }
    
    // 上限と下限を比較して確定しているbitがあればencoded bitとしてバッファに格納する。
    // 確定しているbit分だけ、上限・下限をシフトする。
    while ((lower_bound_ & kMSBIT) == (upper_bound_ & kMSBIT)) {
      unsigned char outbit = lower_bound_ >> (kN-1);
      AddBuffer(outbit);
      lower_bound_ = (lower_bound_ << 1) & kMSMASK;
      upper_bound_ = ((upper_bound_ << 1) & kMSMASK) | 1;
    }
    
    // クローニングを行う。
    DoCloning(bit);

    // マルコフ連鎖を更新する。
    current_state_->SetTransCount(bit, current_state_->GetTransCount(bit)+1);
    current_state_ = current_state_->GetNextState(bit);
  }
  // encodedされた最終bitが、バイトとして出力されるようにダミーの7bitをencodeする。
  // また、encode対象の最終bitが正常にencodeされるように、mpの末尾1bitを除いた全てのbit列をencoded bitとして出力する。
  void EncodeFinish () {
    ulong mp;
    for (int i=0; i<7; i++) {
      mp = CalculateMP();
      // ダミーのbitとして、encoded bitが最低1bit確定されるbitを選択し、encodeする。
      if ((lower_bound_ & kMSBIT) == (mp & kMSBIT)) {
        // lower_bound_の最上位bitとmpの最上位bitが一致する場合は、ダミーのbitとして0をencodeする。
        Encode(0, mp);
      } else {
        // upper_bound_の最上位bitとmpの最上位bitが一致する場合は、ダミーのbitとして1をencodeする。
        Encode(1, mp);
      }
    }
    mp = CalculateMP();
    // mpの最後の1bitを除き、出力する。
    while (mp != kMSBIT) {
      uchar outbit = (mp >> (kN-1));
      AddBuffer(outbit);
      mp = (mp << 1) & kMSMASK;
    }
  }
};
// Dynamic Markov compressionのデコーダクラス
class DmcDecoder : public DmcBase {
public:
  DmcDecoder (int model) : DmcBase (model) {
  }
  void Decode (uchar bit) {
    ulong mp;

    decode_buffer_queue.push_back(bit);

    // decodeされたbit
    char outbit;
    
    // decodeされたbitが確定している間ループし続ける
    do {
      // 現在読み込まれた未確定のencoded bit列から始まるN bit列の最小値・最大値をそれぞれ求める。
      ulong min = 0;
      ulong max = 0;      
      uint count = decode_buffer_queue.size();
      for (uint i=0; i<count; i++) {
        min = (min << 1) + decode_buffer_queue[i];
      }
      min = min << (kN - (count));
      max = min | ((1 << (kN-count)) - 1);

      // 分離点mpとa・bとを比較する。
      mp = CalculateMP();
      if (min >= mp) {
        // 最小値がmp以上の場合、mp以上になることが確定するのでdecodeされたbitは1になる
        outbit = 1;
        lower_bound_ = mp;
      } else if (max < mp) {
        // 最大値がmp未満の場合、mp未満になることが確定するのでdecodeされたbitは0になる
        outbit = 0;
        upper_bound_ = mp - 1;
      } else {
        // mp以上かmp未満かは、次のencoded bitを読み込まないと分からない。
        // decodeされたbitは不明
        outbit = -1;
      }

      if (outbit >= 0) {

        // 上限と下限を比較して確定しているbit分だけ、上限・下限と未確定encoded bit列をシフトする。
        while ((lower_bound_ & kMSBIT) == (upper_bound_ & kMSBIT)) {
          decode_buffer_queue.pop_front();
          lower_bound_ = (lower_bound_ << 1) & kMSMASK;
          upper_bound_ = ((upper_bound_ << 1) & kMSMASK) | 1;
        }

        // クローニングを行う。
        DoCloning(outbit);

        // マルコフ連鎖を更新する。
        current_state_->SetTransCount(outbit, current_state_->GetTransCount(outbit)+1);
        current_state_ = current_state_->GetNextState(outbit);

        AddBuffer(outbit);
      }
    } while (outbit >= 0);
  }
private:
  deque<byte> decode_buffer_queue;
};

void usage() {
  fprintf(stderr, "dmc (e/d) inputfile\n"
          "rc e inputfile     (encode inputfile and output inputfile.dmc)\n"
          "rc e inputfile.dmc (decode inputfile.dmc and make inputfile.dmc.test)\n");
}

// メイン関数
int main (int argc, char* argv[]) {  
  int result;
  int decode = 0;
  int model;
  uint cloning_threshold1 = 0;
  uint cloning_threshold2 = 0;
  while((result=getopt(argc,argv,"edm:A:B:"))!=-1){
    switch(result){
      case 'e': {
        decode = 0; //encode
        break;
      }
      case 'd': {
        decode = 1; //encode
        break;
      }
      case 'm': {
        string str_mode(optarg);
        if (str_mode == "braid") {
          model = MODEL_BRAID;
        } else if (str_mode == "byte") {
          model = MODEL_BYTE;
        } else {
          model = MODEL_BRAID;
        }
        break;
      }
      case 'A': {
        char *ep;
        cloning_threshold1 = strtoumax(optarg, &ep, 10);
        break;
      }
      case 'B': {
        char *ep;
        cloning_threshold2 = strtoumax(optarg, &ep, 10);
        break;
      }
      case ':': {
        usage();
        return -1;
      }
      case '?': {
        usage();
        return -1;
      }
    }
  }

  string infile(argv[optind]);
  FILE* outfp;
  if (decode) {
    // decode
    FILE* infp = fopen(infile.c_str(), "rb");
    if (infp == NULL) {
      fprintf(stderr, "cannot open %s\n", infile.c_str());
      return -1;
    }

    string out_file_name(infile);
    out_file_name += ".raw";
    outfp = fopen(out_file_name.c_str(), "wb");
    if (outfp == NULL) {
      fprintf(stderr, "cannnot open %s\n", out_file_name.c_str());
      return -1;
    }
    DmcDecoder *dd = new DmcDecoder(model);
    dd->SetFilePointer(outfp);
    if (cloning_threshold1 > 0 && cloning_threshold2 > 0) {
      dd->SetCloningThreshold1(cloning_threshold1);
      dd->SetCloningThreshold2(cloning_threshold2);
    }
    int c;
    while ((c = fgetc(infp)) != EOF) {
      unsigned char b = c;
      for (int i=0; i<8; ++i) {
        b = (c >> i) & 1;
        dd->Decode(b);
      }
    }
    printf("%lu\t%lu\n", dd->GetCloningCount(), dd->GetStateCount());
    if (outfp) fclose(outfp);
  } else {
    // encode
    FILE* infp = fopen(infile.c_str(), "rb");
    if (infp == NULL) {
      fprintf(stderr, "cannot open %s\n", infile.c_str());
      return -1;
    }

    string out_file_name(infile);
    out_file_name += ".dmc";
    outfp = fopen(out_file_name.c_str(), "wb");
    if (outfp == NULL) {
      fprintf(stderr, "cannnot open %s\n", out_file_name.c_str());
      return -1;
    }
    DmcEncoder *de = new DmcEncoder(model);
    de->SetFilePointer(outfp);
    if (cloning_threshold1 > 0 && cloning_threshold2 > 0) {
      de->SetCloningThreshold1(cloning_threshold1);
      de->SetCloningThreshold2(cloning_threshold2);
    }
    int c;
    while ((c = fgetc(infp)) != EOF) {
      unsigned char b = c;
      for (int i=0; i<8; ++i) {
        b = (c >> i) & 1;
        de->Encode(b);
      }
    }
    de->EncodeFinish();
    printf("%lu\t%lu\n", de->GetCloningCount(), de->GetStateCount());
    if (outfp) fclose(outfp);
  }
  return 0;
}
